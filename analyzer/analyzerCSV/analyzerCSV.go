// Copyright 2016 Google Inc. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Package analyzer analyzes the uploaded bugreport and displays the results to the user.
package analyzerCSV

import (
	"bytes"
	"errors"
	"fmt"
	"html/template"
	"io"
	"io/ioutil"
	"log"
	"net/http"
	"os"
	"path"
	"regexp"
	"strings"
	"sync"
	"time"

	"github.com/golang/protobuf/proto"

	"github.com/google/battery-historian/activity"
	"github.com/google/battery-historian/broadcasts"
	"github.com/google/battery-historian/bugreportutils"
	"github.com/google/battery-historian/checkindelta"
	"github.com/google/battery-historian/checkinparse"
	"github.com/google/battery-historian/checkinutil"
	"github.com/google/battery-historian/dmesg"
	"github.com/google/battery-historian/historianutils"
	"github.com/google/battery-historian/kernel"
	"github.com/google/battery-historian/packageutils"
	"github.com/google/battery-historian/parseutils"
	"github.com/google/battery-historian/powermonitor"
	"github.com/google/battery-historian/presenter"
	"github.com/google/battery-historian/wearable"

	bspb "github.com/google/battery-historian/pb/batterystats_proto"
	sessionpb "github.com/google/battery-historian/pb/session_proto"
	usagepb "github.com/google/battery-historian/pb/usagestats_proto"
	"encoding/csv"
	"strconv"
)


const (
	// maxFileSize is the maximum file size allowed for uploaded package.
	maxFileSize = 100 * 1024 * 1024 // 100 MB Limit

	minSupportedSDK        = 21 // We only support Lollipop bug reports and above
	numberOfFilesToCompare = 2

	// Historian V2 Log sources
	batteryHistory  = "Battery History"
	broadcastsLog   = "Broadcasts"
	eventLog        = "Event"
	kernelDmesg     = "Kernel Dmesg"
	kernelTrace     = "Kernel Trace"
	lastLogcat      = "Last Logcat"
	locationLog     = "Location"
	powerMonitorLog = "Power Monitor"
	systemLog       = "System"
	wearableLog     = "Wearable"

	// Analyzable file types.
	bugreportFT    = "bugreport"
	bugreport2FT   = "bugreport2"
	kernelFT       = "kernel"
	powerMonitorFT = "powermonitor"
)

var (
	// Initialized in InitTemplates()
	uploadTempl  *template.Template
	resultTempl  *template.Template
	compareTempl *template.Template

	// Initialized in SetScriptsDir()
	scriptsDir    string
	isOptimizedJs bool

	// Initialized in SetResVersion()
	resVersion int

	// batteryRE is a regular expression that matches the time information for battery.
	// e.g. 9,0,l,bt,0,86546081,70845214,99083316,83382448,1458155459650,83944766,68243903
	batteryRE = regexp.MustCompile(`9,0,l,bt,(?P<batteryTime>.*)`)
)

type historianData struct {
	html string
	err  error
}

type csvData struct {
	csv  string
	errs []error
}

type historianV2Log struct {
	// Log source that the CSV is generated from.
	// e.g. "batteryhistory" or "eventlog".
	Source string `json:"source"`
	CSV    string `json:"csv"`
	// Optional start time of the log as unix time in milliseconds.
	StartMs int64 `json:"startMs"`
}

type uploadResponse struct {
	SDKVersion          int                      `json:"sdkVersion"`
	HistorianV2Logs     []historianV2Log         `json:"historianV2Logs"`
	LevelSummaryCSV     string                   `json:"levelSummaryCsv"`
	DisplayPowerMonitor bool                     `json:"displayPowerMonitor"`
	ReportVersion       int32                    `json:"reportVersion"`
	AppStats            []presenter.AppStat      `json:"appStats"`
	BatteryStats        *bspb.BatteryStats       `json:"batteryStats"`
	DeviceCapacity      float32                  `json:"deviceCapacity"`
	HistogramStats      presenter.HistogramStats `json:"histogramStats"`
	TimeToDelta         map[string]string        `json:"timeToDelta"`
	CriticalError       string                   `json:"criticalError"` // Critical errors are ones that cause parsing of important data to abort early and should be shown prominently to the user.
	Note                string                   `json:"note"`          // A message to show to the user that they should be aware of.
	FileName            string                   `json:"fileName"`
	Location            string                   `json:"location"`
	OverflowMs          int64                    `json:"overflowMs"`
	IsDiff              bool                     `json:"isDiff"`
}

type uploadResponseCompare struct {
	UploadResponse  []uploadResponse                 `json:"UploadResponse"`
	HTML            string                           `json:"html"`
	UsingComparison bool                             `json:"usingComparison"`
	CombinedCheckin presenter.CombinedCheckinSummary `json:"combinedCheckin"`
	SystemUIDecoder activity.SystemUIDecoder         `json:"systemUiDecoder"`
}

type summariesData struct {
	summaries       []parseutils.ActivitySummary
	historianV2CSV  string
	levelSummaryCSV string
	timeToDelta     map[string]string
	errs            []error
	overflowMs      int64
}

type checkinData struct {
	batterystats *bspb.BatteryStats
	warnings     []string
	err          []error
}

// UploadedFile is a user uploaded bugreport or its associated file to be analyzed.
type UploadedFile struct {
	FileType string
	FileName string
	Contents []byte
}

// ParsedData holds the extracted details from the parsing of each file.
type ParsedData struct {
	// The kernel trace file needs to be processed with a bug report, so we save the file names here to be processed after reading in all the files.
	bugReport string
	// Error if bugreport could not be saved.
	brSaveErr   error
	kernelTrace string
	// Error if kernel trace file could not be saved.
	kernelSaveErr error
	deviceType    string

	responseArr []uploadResponse
	kd          *csvData
	md          *csvData
	data        []presenter.HTMLData
}

// BatteryStatsInfo holds the extracted batterystats details for a bugreport.
type BatteryStatsInfo struct {
	Filename string
	Stats    *bspb.BatteryStats
	Meta     *bugreportutils.MetaInfo
}


//mod_func

func file_is_exists(f string) bool {
	_, err := os.Stat(f)
	if os.IsNotExist(err) {
		return false
	}
	return err == nil
}

//mod_func_kanak




// Cleanup removes all temporary files written by the ParsedData analyzer.
// Should be called after ParsedData is no longer needed.
func (pd *ParsedData) Cleanup() {
	if pd.bugReport != "" {
		os.Remove(pd.bugReport)
	}
	if pd.kernelTrace != "" {
		os.Remove(pd.kernelTrace)
	}
}



// parsePowerMonitorFile processes the power monitor file and stores the result in the ParsedData.
func (pd *ParsedData) parsePowerMonitorFile(fname, contents string) error {
	if valid, output, extraErrs := powermonitor.Parse(contents); valid {
		pd.md = &csvData{output, extraErrs}
		return nil
	}
	return fmt.Errorf("%v: invalid power monitor file", fname)
}

// templatePath expands a template filename into a full resource path for that template.
func templatePath(dir, tmpl string) string {
	if len(dir) == 0 {
		dir = "./templates"
	}
	return path.Join(dir, tmpl)
}

// scriptsPath expands the script filename into a full resource path for the script.
func scriptsPath(dir, script string) string {
	if len(dir) == 0 {
		dir = "./scripts"
	}
	return path.Join(dir, script)
}

// InitTemplates initializes the HTML templates after google.Init() is called.
// google.Init() must be called before resources can be accessed.
func InitTemplates(dir string) {
	uploadTempl = constructTemplate(dir, []string{
		"base.html",
		"body.html",
		"upload.html",
		"copy.html",
	})

	// base.html is intentionally excluded from resultTempl. resultTempl is loaded into the HTML
	// generated by uploadTempl, so attempting to include base.html here causes some of the
	// javascript files to be imported twice, which causes things to start blowing up.
	resultTempl = constructTemplate(dir, []string{
		"body.html",
		"summaries.html",
		"historian_v2.html",
		"checkin.html",
		"history.html",
		"appstats.html",
		"tables.html",
		"tablesidebar.html",
		"histogramstats.html",
		"powerstats.html",
	})

	compareTempl = constructTemplate(dir, []string{
		"body.html",
		"compare_summaries.html",
		"compare_checkin.html",
		"compare_history.html",
		"historian_v2.html",
		"tablesidebar.html",
		"tables.html",
		"appstats.html",
		"histogramstats.html",
	})
}

// constructTemplate returns a new template constructed from parsing the template
// definitions from the files with the given base directory and filenames.
func constructTemplate(dir string, files []string) *template.Template {
	var paths []string
	for _, f := range files {
		paths = append(paths, templatePath(dir, f))
	}
	return template.Must(template.ParseFiles(paths...))
}

// SetScriptsDir sets the directory of the Historian and kernel trace Python scripts.
func SetScriptsDir(dir string) {
	scriptsDir = dir
}

// SetResVersion sets the current version to force reloading of JS and CSS files.
func SetResVersion(v int) {
	resVersion = v
}

// SetIsOptimized sets whether the JS will be optimized.
func SetIsOptimized(optimized bool) {
	isOptimizedJs = optimized
}

// closeConnection closes the http connection and writes a response.
func closeConnection(w http.ResponseWriter, s string) {
	if flusher, ok := w.(http.Flusher); ok {
		w.Header().Set("Connection", "close")
		w.Header().Set("Content-Length", fmt.Sprintf("%d", len(s)))
		w.WriteHeader(http.StatusExpectationFailed)
		io.WriteString(w, s)
		flusher.Flush()
	}
	log.Println(s, " Closing connection.")
	conn, _, _ := w.(http.Hijacker).Hijack()
	conn.Close()
}

// UploadHandler serves the upload html page.
func UploadHandler(w http.ResponseWriter, r *http.Request) {
	// If false, the upload template will load closure and js files in the header.
	uploadData := struct {
		IsOptimizedJs bool
		ResVersion    int
	}{
		isOptimizedJs,
		resVersion,
	}

	if err := uploadTempl.Execute(w, uploadData); err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}
}

// HTTPAnalyzeHandler processes the bugreport package uploaded via an http request's multipart body.
func HTTPAnalyzeHandler(w http.ResponseWriter, r *http.Request) {
	// Do not accept files that are greater than 100 MBs.
	if r.ContentLength > maxFileSize {
		closeConnection(w, "File too large (>100MB).")
		return
	}
	r.Body = http.MaxBytesReader(w, r.Body, maxFileSize)
	log.Printf("Trace starting reading uploaded file. %d bytes", r.ContentLength)
	defer log.Printf("Trace ended analyzing file.")

	//get the multipart reader for the request.
	reader, err := r.MultipartReader()
	if err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}
	fs := make(map[string]UploadedFile)
	//copy each part to destination.
	for {
		part, err := reader.NextPart()
		if err == io.EOF {
			break
		}

		// If part.FileName() is empty, skip this iteration.
		if part.FileName() == "" {
			continue
		}

		b, err := ioutil.ReadAll(part)
		if err != nil {
			http.Error(w, "Failed to read file. Please try again.", http.StatusInternalServerError)
			return
		}
		if len(b) == 0 {
			continue
		}

		//kanak//files, err := bugreportutils.Contents(part.FileName(), b)

		///added blocks by kanak

		//added new kanak//
		directoryName := "F:/bugreports"
		bugZips, err := ioutil.ReadDir(directoryName)
		if err != nil {
			log.Fatal(err)
		}
		//added new kanak/
		var counterGlobal int64=0
		for _, b_f := range bugZips {
			counterGlobal++
			log.Println(b_f.Name())
			//debugDone//ca, err := ioutil.ReadFile(directoryName + "/" + f.Name())
			//debugDone//Print(err)
			//debugDone//log.Print(ca)


			//files, err := bugreportutils.Contents(part.FileName(), b)
			//debugCOmment//filePath:="C:/adb/bugreport-N2G47H-2018-04-22-23-47-36.zip"
			filePath:=directoryName + "/" + b_f.Name()
			b, err = ioutil.ReadFile(filePath)
			//log.Print(b)
			files, err := bugreportutils.Contents(b_f.Name(), b)
			//log.Print(files)
			//br, files, err := bugreportutils.ExtractBugReport(filePath, b)
			//log.Print(br)

			///adeed blocks end here

			if err != nil {
				http.Error(w, fmt.Sprintf("failed to read file contents: %v", err), http.StatusInternalServerError)
				return
			}

			var contents []byte
			valid := false
			fname := ""
		contentLoop:
			for n, f := range files {
				switch part.FormName() {
				case "bugreport", "bugreport2":
					if bugreportutils.IsBugReport(f) {
						// TODO: handle the case of additional kernel and power monitor files within a single uploaded file
						valid = true
						contents = f
						fname = n
						break contentLoop
					}
				case "kernel":
					if kernel.IsTrace(f) {
						valid = true
						contents = f
						fname = n
						break contentLoop
					}
				case "powermonitor":
					if powermonitor.IsValid(f) {
						valid = true
						contents = f
						fname = n
						break contentLoop
					}
				default:
					valid = true
					contents = f
					fname = n
					break contentLoop
				}
			}

			if !valid {
				http.Error(w, fmt.Sprintf("%s does not contain a valid %s file", part.FileName(), part.FormName()), http.StatusInternalServerError)
				return
			}

			fs[part.FormName()] = UploadedFile{part.FormName(), fname, contents}
		}
	//commentKanak
	AnalyzeAndResponse(fs, counterGlobal, "not_possible", "not_at_all_now_here")



		//pd := &ParsedData{}
		//
		//fB, okB := fs[bugreportFT]
		//if !okB {
		//
		//}
		//
		//// Parse the bugreport.
		//fB2 := fs[bugreport2FT]
		//if err := pd.parseBugReportMOd(fB.FileName, string(fB.Contents), fB2.FileName, string(fB2.Contents), counterGlobal); err != nil {
		//	log.Print("GOt problem bro!")
		//}


	}
	}

// AnalyzeAndResponse analyzes the uploaded files and sends the HTTP response in JSON.
func AnalyzeAndResponse( files map[string]UploadedFile,counterGlobal int64 , fileNameCSV string, outputDir string) {
	pd := &ParsedData{}
	defer pd.Cleanup()
	if err := pd.AnalyzeFiles(files,counterGlobal, fileNameCSV, outputDir); err != nil {
		//http.Error( fmt.Sprintf("failed to analyze file: %v", err), http.StatusInternalServerError)
		return
	}
//	pd.SendAsJSON(w, r)
}

// AnalyzeFiles processes and analyzes the list of uploaded files.
func (pd *ParsedData) AnalyzeFiles(files map[string]UploadedFile, counterGlobal int64, fileNameCSV string, outputDir string) error {
	fB, okB := files[bugreportFT]
	if !okB {
		return errors.New("missing bugreport file")
	}

	// Parse the bugreport.
	fB2 := files[bugreport2FT]
	if err := pd.parseBugReport(fB.FileName, string(fB.Contents), fB2.FileName, string(fB2.Contents), counterGlobal, fileNameCSV, outputDir); err != nil {
		return fmt.Errorf("error parsing bugreport: %v", err)
	}
	// Write the bug report to a file in case we need it to process a kernel trace file.
	if len(pd.data) < numberOfFilesToCompare {
		tmpFile, err := writeTempFile(string(fB.Contents))
		if err != nil {
			return fmt.Errorf("could not write bugreport: %v", err)
		}
		pd.bugReport = tmpFile
	}
	if file, ok := files[kernelFT]; ok {
		if !kernel.IsTrace(file.Contents) {
			return fmt.Errorf("invalid kernel trace file: %v", file.FileName)
		}
		if pd.kernelTrace != "" {
			log.Printf("more than one kernel trace file found")
		} else {
			// Need bug report to process kernel trace file, so store the file for later processing.
			tmpFile, err := writeTempFile(string(file.Contents))
			if err != nil {
				return fmt.Errorf("could not write kernel trace file: %v", err)
			}
			pd.kernelTrace = tmpFile
		}
	}
	if file, ok := files[powerMonitorFT]; ok {
		// Parse the power monitor file.
		if err := pd.parsePowerMonitorFile(file.FileName, string(file.Contents)); err != nil {
			return fmt.Errorf("error parsing power monitor file: %v", err)
		}
	}

	return nil
}

// extractHistogramStats retrieves the data needed to draw the histogram charts.
func extractHistogramStats(data presenter.HTMLData) presenter.HistogramStats {
	return presenter.HistogramStats{
		ScreenOffDischargeRatePerHr:         data.CheckinSummary.ScreenOffDischargeRatePerHr,
		ScreenOnDischargeRatePerHr:          data.CheckinSummary.ScreenOnDischargeRatePerHr,
		ScreenOffUptimePercentage:           data.CheckinSummary.ScreenOffUptimePercentage,
		ScreenOnTimePercentage:              data.CheckinSummary.ScreenOnTimePercentage,
		PartialWakelockTimePercentage:       data.CheckinSummary.PartialWakelockTimePercentage,
		KernelOverheadTimePercentage:        data.CheckinSummary.KernelOverheadTimePercentage,
		SignalScanningTimePercentage:        data.CheckinSummary.SignalScanningTimePercentage,
		MobileActiveTimePercentage:          data.CheckinSummary.MobileActiveTimePercentage,
		MobileKiloBytesPerHr:                data.CheckinSummary.MobileKiloBytesPerHr,
		WifiKiloBytesPerHr:                  data.CheckinSummary.WifiKiloBytesPerHr,
		PhoneCallTimePercentage:             data.CheckinSummary.PhoneCallTimePercentage,
		DeviceIdlingTimePercentage:          data.CheckinSummary.DeviceIdlingTimePercentage,
		FullWakelockTimePercentage:          data.CheckinSummary.FullWakelockTimePercentage,
		InteractiveTimePercentage:           data.CheckinSummary.InteractiveTimePercentage,
		DeviceIdleModeEnabledTimePercentage: data.CheckinSummary.DeviceIdleModeEnabledTimePercentage,
		TotalAppGPSUseTimePerHour:           data.CheckinSummary.TotalAppGPSUseTimePerHour,
		BluetoothOnTimePercentage:           data.CheckinSummary.BluetoothOnTimePercentage,
		LowPowerModeEnabledTimePercentage:   data.CheckinSummary.LowPowerModeEnabledTimePercentage,
		TotalAppANRCount:                    data.CheckinSummary.TotalAppANRCount,
		TotalAppCrashCount:                  data.CheckinSummary.TotalAppCrashCount,
		WifiDischargeRatePerHr:              data.CheckinSummary.WifiDischargeRatePerHr,
		BluetoothDischargeRatePerHr:         data.CheckinSummary.BluetoothDischargeRatePerHr,
		ModemDischargeRatePerHr:             data.CheckinSummary.ModemDischargeRatePerHr,
		WifiOnTimePercentage:                data.CheckinSummary.WifiOnTimePercentage,
		WifiTransferTimePercentage:          data.CheckinSummary.WifiTransferTimePercentage,
		BluetoothTransferTimePercentage:     data.CheckinSummary.BluetoothTransferTimePercentage,
		ModemTransferTimePercentage:         data.CheckinSummary.ModemTransferTimePercentage,
		TotalAppSyncsPerHr:                  data.CheckinSummary.TotalAppSyncsPerHr,
		TotalAppWakeupsPerHr:                data.CheckinSummary.TotalAppWakeupsPerHr,
		TotalAppCPUPowerPct:                 data.CheckinSummary.TotalAppCPUPowerPct,
		TotalAppFlashlightUsePerHr:          data.CheckinSummary.TotalAppFlashlightUsePerHr,
		TotalAppCameraUsePerHr:              data.CheckinSummary.TotalAppCameraUsePerHr,
		ScreenBrightness:                    data.CheckinSummary.ScreenBrightness,
		SignalStrength:                      data.CheckinSummary.SignalStrength,
		WifiSignalStrength:                  data.CheckinSummary.WifiSignalStrength,
		BluetoothState:                      data.CheckinSummary.BluetoothState,
		DataConnection:                      data.CheckinSummary.DataConnection,
	}
}

// writeTempFile writes the contents to a temporary file.
func writeTempFile(contents string) (string, error) {
	tmpFile, err := ioutil.TempFile("", "historian")
	if err != nil {
		return "", err
	}
	tmpFile.WriteString(contents)
	if err := tmpFile.Close(); err != nil {
		os.Remove(tmpFile.Name())
		return "", err
	}
	return tmpFile.Name(), nil
}

// parseBugReport analyzes the given bug report contents, and updates the ParsedData object.
// contentsB is an optional second bug report. If it's given and the Android IDs and batterystats
// checkin start times are the same, a diff of the checkins will be saved, otherwise, they will be
// saved as separate reports.
func (pd *ParsedData) parseBugReport(fnameA, contentsA, fnameB, contentsB string, counterGlobal int64, fileNameCSV string, outputDir string) error {

	doActivity := func(ch chan activity.LogsData, contents string, pkgs []*usagepb.PackageInfo) {
		ch <- activity.Parse(pkgs, contents)
	}

	doBroadcasts := func(ch chan csvData, contents string) {
		csv, errs := broadcasts.Parse(contents)
		ch <- csvData{csv: csv, errs: errs}
	}

	doCheckin := func(ch chan checkinData, meta *bugreportutils.MetaInfo, bs string, pkgs []*usagepb.PackageInfo) {
		var ctr checkinutil.IntCounter
		s := &sessionpb.Checkin{
			Checkin:          proto.String(bs),
			BuildFingerprint: proto.String(meta.BuildFingerprint),
		}
		stats, warnings, errs := checkinparse.ParseBatteryStats(&ctr, checkinparse.CreateBatteryReport(s), pkgs)
		if stats == nil {
			errs = append(errs, errors.New("could not parse aggregated battery stats"))
		} else {
			pd.deviceType = stats.GetBuild().GetDevice()
		}
		ch <- checkinData{stats, warnings, errs}
		log.Printf("Trace finished processing checkin.")
	}

	doDmesg := func(ch chan dmesg.Data, contents string) {
		ch <- dmesg.Parse(contents)
	}

	doHistorian := func(ch chan historianData, fname, contents string) {
		// Create a temporary file to save the bug report, for the Historian script.
		brFile, err := writeTempFile(contents)
		if err != nil {
			ch <- historianData{err: err}
			return
		}
		// Don't run the Historian script if it could not create temporary file.
		defer os.Remove(brFile)
		html, err := generateHistorianPlot(fname, brFile)
		ch <- historianData{html, err}
		log.Printf("Trace finished generating Historian plot.")
	}

	// bs is the batterystats section of the bug report
	doSummaries := func(ch chan summariesData, bs string, pkgs []*usagepb.PackageInfo) {
		ch <- analyze(bs, pkgs)
		log.Printf("Trace finished processing summary data.")
	}

	doWearable := func(ch chan string, loc, contents string) {
		if valid, output, _ := wearable.Parse(contents, loc); valid {
			ch <- output
		} else {
			ch <- ""
		}
	}

	type brData struct {
		fileName string
		contents string
		meta     *bugreportutils.MetaInfo
		bt       *bspb.BatteryStats_System_Battery
		dt       time.Time
	}

	// doParsing needs to be declared before its initialization so that it can call itself recursively.
	var doParsing func(brDA, brDB *brData)
	// The earlier report will be subtracted from the later report.
	doParsing = func(brDA, brDB *brData) {
		if brDA == nil && brDB == nil {
			return
		}
		if brDA.fileName == "" || brDA.contents == "" {
			return
		}

		// Check to see if we should do a stats diff of the two bug reports.
		diff := brDA != nil && brDB != nil &&
			// Requires that the second report's contents are not empty.
			brDB.fileName != "" && brDB.contents != "" &&
			// Android IDs must be the same.
			brDA.meta.DeviceID == brDB.meta.DeviceID &&
			// Batterystats start clock time must be the same.
			brDA.bt != nil && brDB.bt != nil &&
			brDA.bt.GetStartClockTimeMsec() == brDB.bt.GetStartClockTimeMsec()
		var earl, late *brData
		if !diff {
			if brDB != nil {
				var wg sync.WaitGroup
				// Need to parse each report separately.
				wg.Add(1)
				go func() {
					defer wg.Done()
					doParsing(brDA, nil)
				}()
				wg.Add(1)
				go func() {
					defer wg.Done()
					doParsing(brDB, nil)
				}()
				wg.Wait()
				return
			}
			// Only one report given. This can be parsed on its own.
			late = brDA
		} else if brDB.dt.Equal(brDA.dt) {
			// In the off chance that the times are exactly equal (it's at the second
			// granularity), set the report with the longer realtime as the later one.
			if brDB.bt.GetTotalRealtimeMsec() > brDA.bt.GetTotalRealtimeMsec() {
				earl, late = brDA, brDB
			} else {
				earl, late = brDB, brDA
			}
		} else if brDB.dt.Before(brDA.dt) {
			earl, late = brDB, brDA
		} else {
			earl, late = brDA, brDB
		}

		if diff {
			log.Printf("Trace started diffing files.")
		} else {
			log.Printf("Trace started analyzing %q file.", brDA.fileName)
		}

		// Generate the Historian plot and Volta parsing simultaneously.
		historianCh := make(chan historianData)
		summariesCh := make(chan summariesData)
		activityManagerCh := make(chan activity.LogsData)
		broadcastsCh := make(chan csvData)
		dmesgCh := make(chan dmesg.Data)
		wearableCh := make(chan string)
		var checkinL, checkinE checkinData
		var warnings []string
		var bsStats *bspb.BatteryStats
		var errs []error
		supV := late.meta.SdkVersion >= minSupportedSDK && (!diff || earl.meta.SdkVersion >= minSupportedSDK)

		ce := ""

		// Only need to generate it for the later report.
		go doHistorian(historianCh, late.fileName, late.contents)
		if !supV {
			ce = "Unsupported bug report version."
			errs = append(errs, errors.New("unsupported bug report version"))
		} else {
			// No point running these if we don't support the sdk version since we won't get any data from them.

			bsL := bugreportutils.ExtractBatterystatsCheckin(late.contents)
			if strings.Contains(bsL, "Exception occurred while dumping") {
				ce = "Exception found in battery dump."
				errs = append(errs, errors.New("exception found in battery dump"))
			}

			pkgsL, pkgErrs := packageutils.ExtractAppsFromBugReport(late.contents)
			errs = append(errs, pkgErrs...)
			checkinECh := make(chan checkinData)
			checkinLCh := make(chan checkinData)
			go doCheckin(checkinLCh, late.meta, bsL, pkgsL)
			if diff {
				// Calculate batterystats for the earlier report.
				bsE := bugreportutils.ExtractBatterystatsCheckin(earl.contents)
				if strings.Contains(bsE, "Exception occurred while dumping") {
					ce = "Exception found in battery dump."
					errs = append(errs, errors.New("exception found in battery dump"))
				}
				pkgsE, pkgErrs := packageutils.ExtractAppsFromBugReport(earl.contents)
				errs = append(errs, pkgErrs...)
				go doCheckin(checkinECh, earl.meta, bsE, pkgsE)
			}

			// These are only parsed for supported sdk versions, even though they are still
			// present in unsupported sdk version reports, because the events are rendered
			// with Historian v2, which is not generated for unsupported sdk versions.
			go doActivity(activityManagerCh, late.contents, pkgsL)
			go doBroadcasts(broadcastsCh, late.contents)
			go doDmesg(dmesgCh, late.contents)
			go doWearable(wearableCh, late.dt.Location().String(), late.contents)
			go doSummaries(summariesCh, bsL, pkgsL)



			log.Println(checkinE.batterystats)  /////
			checkinL = <-checkinLCh
			errs = append(errs, checkinL.err...)
			warnings = append(warnings, checkinL.warnings...)
			if diff {
				checkinE = <-checkinECh
				errs = append(errs, checkinE.err...)
				warnings = append(warnings, checkinE.warnings...)
			}
			if checkinL.batterystats == nil || (diff && checkinE.batterystats == nil) {
				ce = "Could not parse aggregated battery stats."
			} else if diff {
				bsStats = checkindelta.ComputeDeltaFromSameDevice(checkinL.batterystats, checkinE.batterystats)
			} else {
				bsStats = checkinL.batterystats
			}
		}

		historianOutput := <-historianCh
		if historianOutput.err != nil {
			historianOutput.html = fmt.Sprintf("Error generating historian plot: %v", historianOutput.err)
		}

		var summariesOutput summariesData
		var activityManagerOutput activity.LogsData
		var broadcastsOutput csvData
		var dmesgOutput dmesg.Data
		var wearableOutput string

		if supV {
			summariesOutput = <-summariesCh
			activityManagerOutput = <-activityManagerCh
			broadcastsOutput = <-broadcastsCh
			dmesgOutput = <-dmesgCh
			wearableOutput = <-wearableCh
			errs = append(errs, append(broadcastsOutput.errs, append(dmesgOutput.Errs, append(summariesOutput.errs, activityManagerOutput.Errs...)...)...)...)
		}


		/////////////////////////////////////////////////////////////////////
		////Appedned Block by Kanak Starts
		totAppCount:=len(bsStats.App)+1


		csvModOutput := make([][]string, totAppCount)
		//csvModOutput:=[10000][100]string{}
		intd:=0
		for _, appRec := range bsStats.App{
			if appRec != nil {
				csvModOutput[intd]=make([]string,85)
				csvModOutput[intd][0]=bsStats.App[intd].GetName()
				csvModOutput[intd][1]=strconv.FormatFloat(float64(bsStats.App[intd].Cpu.GetPowerMaMs()),'f', 6, 32)
				csvModOutput[intd][2]=strconv.FormatFloat(float64(bsStats.App[intd].Cpu.GetSystemTimeMs()),'f', 6, 32)
				csvModOutput[intd][3]=strconv.FormatFloat(float64(bsStats.App[intd].Cpu.GetUserTimeMs()),'f', 6, 32)
				csvModOutput[intd][4]=strconv.FormatFloat(float64(bsStats.App[intd].Foreground.GetCount()),'f', 6, 32)
				csvModOutput[intd][5]=strconv.FormatFloat(float64(bsStats.App[intd].Foreground.GetTotalTimeMsec()),'f', 6, 32)
				if bsStats.App[intd].HeadChild !=nil {
					csvModOutput[intd][6]=strconv.FormatFloat(float64(bsStats.App[intd].HeadChild.Apk.GetWakeups()),'f', 6, 32)
				}

				csvModOutput[intd][7]=strconv.FormatFloat(float64(bsStats.App[intd].Camera.GetCount()),'f', 6, 32)
				csvModOutput[intd][8]=strconv.FormatFloat(float64(bsStats.App[intd].Camera.GetTotalTimeMsec()),'f', 6, 32)
				csvModOutput[intd][9]=strconv.FormatFloat(float64(bsStats.App[intd].Flashlight.GetCount()),'f', 6, 32)
				csvModOutput[intd][10]=strconv.FormatFloat(float64(bsStats.App[intd].Flashlight.GetTotalTimeMsec()),'f', 6, 32)
				csvModOutput[intd][11]=strconv.FormatFloat(float64(bsStats.App[intd].BluetoothController.GetIdleTimeMsec()),'f', 6, 32)
				csvModOutput[intd][12]=strconv.FormatFloat(float64(bsStats.App[intd].BluetoothController.GetPowerMah()),'f', 6, 32)
				csvModOutput[intd][13]=strconv.FormatFloat(float64(bsStats.App[intd].BluetoothController.GetRxTimeMsec()),'f', 6, 32)
				csvModOutput[intd][14]=strconv.FormatFloat(float64(bsStats.App[intd].BluetoothMisc.GetBleScanActualTimeMsec()),'f', 6, 32)
				csvModOutput[intd][15]=strconv.FormatFloat(float64(bsStats.App[intd].BluetoothMisc.GetBleScanCount()),'f', 6, 32)
				csvModOutput[intd][16]=strconv.FormatFloat(float64(bsStats.App[intd].BluetoothMisc.GetBleScanTimeMsec()),'f', 6, 32)
				csvModOutput[intd][17]=strconv.FormatFloat(float64(bsStats.App[intd].BluetoothMisc.GetBleScanCountBg()),'f', 6, 32)
				csvModOutput[intd][18]=strconv.FormatFloat(float64(bsStats.App[intd].BluetoothMisc.GetBleScanResultCount()),'f', 6, 32)
				csvModOutput[intd][19]=strconv.FormatFloat(float64(bsStats.App[intd].BluetoothMisc.GetBleScanActualTimeMsecBg()),'f', 6, 32)
				csvModOutput[intd][20]=strconv.FormatFloat(float64(bsStats.App[intd].StateTime.GetActiveTimeMsec()),'f', 6, 32)
				csvModOutput[intd][21]=strconv.FormatFloat(float64(bsStats.App[intd].StateTime.GetBackgroundTimeMsec()),'f', 6, 32)
				csvModOutput[intd][22]=strconv.FormatFloat(float64(bsStats.App[intd].StateTime.GetCachedTimeMsec()),'f', 6, 32)
				csvModOutput[intd][23]=strconv.FormatFloat(float64(bsStats.App[intd].StateTime.GetForegroundServiceTimeMsec()),'f', 6, 32)
				csvModOutput[intd][24]=strconv.FormatFloat(float64(bsStats.App[intd].StateTime.GetForegroundTimeMsec()),'f', 6, 32)
				csvModOutput[intd][25]=strconv.FormatFloat(float64(bsStats.App[intd].StateTime.GetTopSleepingTimeMsec()),'f', 6, 32)
				csvModOutput[intd][26]=strconv.FormatFloat(float64(bsStats.App[intd].StateTime.GetTopTimeMsec()),'f', 6, 32)
				csvModOutput[intd][27]=strconv.FormatFloat(float64(bsStats.App[intd].ModemController.GetIdleTimeMsec()),'f', 6, 32)
				csvModOutput[intd][28]=strconv.FormatFloat(float64(bsStats.App[intd].ModemController.GetPowerMah()),'f', 6, 32)
				csvModOutput[intd][29]=strconv.FormatFloat(float64(bsStats.App[intd].ModemController.GetRxTimeMsec()),'f', 6, 32)
				csvModOutput[intd][30]=strconv.FormatFloat(float64(bsStats.App[intd].Network.GetBtBytesRx()),'f', 6, 32)
				csvModOutput[intd][31]=strconv.FormatFloat(float64(bsStats.App[intd].Network.GetBtBytesTx()),'f', 6, 32)
				csvModOutput[intd][32]=strconv.FormatFloat(float64(bsStats.App[intd].Network.GetMobileActiveCount()),'f', 6, 32)
				csvModOutput[intd][33]=strconv.FormatFloat(float64(bsStats.App[intd].Network.GetMobileActiveTimeMsec()),'f', 6, 32)
				csvModOutput[intd][34]=strconv.FormatFloat(float64(bsStats.App[intd].Network.GetMobileBytesBgRx()),'f', 6, 32)
				csvModOutput[intd][35]=strconv.FormatFloat(float64(bsStats.App[intd].Network.GetMobileBytesBgTx()),'f', 6, 32)
				csvModOutput[intd][36]=strconv.FormatFloat(float64(bsStats.App[intd].Network.GetMobilePacketsBgRx()),'f', 6, 32)
				csvModOutput[intd][37]=strconv.FormatFloat(float64(bsStats.App[intd].Network.GetMobilePacketsBgTx()),'f', 6, 32)
				csvModOutput[intd][38]=strconv.FormatFloat(float64(bsStats.App[intd].Network.GetMobilePacketsRx()),'f', 6, 32)
				csvModOutput[intd][39]=strconv.FormatFloat(float64(bsStats.App[intd].Network.GetMobilePacketsTx()),'f', 6, 32)
				csvModOutput[intd][40]=strconv.FormatFloat(float64(bsStats.App[intd].Network.GetMobileWakeupCount()),'f', 6, 32)
				csvModOutput[intd][41]=strconv.FormatFloat(float64(bsStats.App[intd].Network.GetBtBytesTx()),'f', 6, 32)
				csvModOutput[intd][42]=strconv.FormatFloat(float64(bsStats.App[intd].Network.GetMobileBytesRx()),'f', 6, 32)
				csvModOutput[intd][43]=strconv.FormatFloat(float64(bsStats.App[intd].Network.GetMobileBytesTx()),'f', 6, 32)
				csvModOutput[intd][44]=strconv.FormatFloat(float64(bsStats.App[intd].Network.GetWifiBytesRx()),'f', 6, 32)
				csvModOutput[intd][45]=strconv.FormatFloat(float64(bsStats.App[intd].Network.GetWifiBytesTx()),'f', 6, 32)
				csvModOutput[intd][46]=strconv.FormatFloat(float64(bsStats.App[intd].Network.GetWifiBytesBgRx()),'f', 6, 32)
				csvModOutput[intd][47]=strconv.FormatFloat(float64(bsStats.App[intd].Network.GetWifiBytesBgTx()),'f', 6, 32)
				csvModOutput[intd][48]=strconv.FormatFloat(float64(bsStats.App[intd].Network.GetWifiPacketsBgRx()),'f', 6, 32)
				csvModOutput[intd][49]=strconv.FormatFloat(float64(bsStats.App[intd].Network.GetWifiPacketsBgTx()),'f', 6, 32)
				csvModOutput[intd][50]=strconv.FormatFloat(float64(bsStats.App[intd].Network.GetWifiPacketsRx()),'f', 6, 32)
				csvModOutput[intd][51]=strconv.FormatFloat(float64(bsStats.App[intd].Network.GetWifiPacketsTx()),'f', 6, 32)
				csvModOutput[intd][52]=strconv.FormatFloat(float64(bsStats.App[intd].Network.GetWifiWakeupCount()),'f', 6, 32)
				csvModOutput[intd][53]=strconv.FormatFloat(float64(bsStats.App[intd].Audio.GetCount()),'f', 6, 32)
				csvModOutput[intd][54]=strconv.FormatFloat(float64(bsStats.App[intd].Audio.GetTotalTimeMsec()),'f', 6, 32)
				csvModOutput[intd][55]=strconv.FormatFloat(float64(bsStats.App[intd].Video.GetCount()),'f', 6, 32)
				csvModOutput[intd][56]=strconv.FormatFloat(float64(bsStats.App[intd].Video.GetTotalTimeMsec()),'f', 6, 32)
				csvModOutput[intd][57]=strconv.FormatFloat(float64(bsStats.App[intd].WifiController.GetIdleTimeMsec()),'f', 6, 32)
				csvModOutput[intd][58]=strconv.FormatFloat(float64(bsStats.App[intd].WifiController.GetPowerMah()),'f', 6, 32)
				csvModOutput[intd][59]=strconv.FormatFloat(float64(bsStats.App[intd].WifiController.GetRxTimeMsec()),'f', 6, 32)
				csvModOutput[intd][60]=strconv.FormatFloat(float64(bsStats.App[intd].Wifi.GetFullWifiLockTimeMsec()),'f', 6, 32)
				csvModOutput[intd][61]=strconv.FormatFloat(float64(bsStats.App[intd].Wifi.GetRxTimeMsec()),'f', 6, 32)
				csvModOutput[intd][62]=strconv.FormatFloat(float64(bsStats.App[intd].Wifi.GetTxTimeMsec()),'f', 6, 32)
				csvModOutput[intd][63]=strconv.FormatFloat(float64(bsStats.App[intd].Wifi.GetIdleTimeMsec()),'f', 6, 32)
				csvModOutput[intd][64]=strconv.FormatFloat(float64(bsStats.App[intd].Wifi.GetRunningTimeMsec()),'f', 6, 32)
				csvModOutput[intd][65]=strconv.FormatFloat(float64(bsStats.App[intd].Wifi.GetScanCount()),'f', 6, 32)
				csvModOutput[intd][66]=strconv.FormatFloat(float64(bsStats.App[intd].Wifi.GetScanCountBg()),'f', 6, 32)
				csvModOutput[intd][67]=strconv.FormatFloat(float64(bsStats.App[intd].Wifi.GetScanTimeMsec()),'f', 6, 32)
				csvModOutput[intd][68]=strconv.FormatFloat(float64(bsStats.App[intd].Wifi.GetScanActualTimeMsec()),'f', 6, 32)
				csvModOutput[intd][69]=strconv.FormatFloat(float64(bsStats.App[intd].Wifi.GetScanActualTimeMsecBg()),'f', 6, 32)
				csvModOutput[intd][70]=strconv.FormatFloat(float64(bsStats.App[intd].PowerUseItem.GetComputedPowerMah()),'f', 6, 32)
				csvModOutput[intd][71]=strconv.FormatFloat(float64(bsStats.App[intd].Vibrator.GetTotalTimeMsec()),'f', 6, 32)
				csvModOutput[intd][72]=strconv.FormatFloat(float64(bsStats.App[intd].Vibrator.GetCount()),'f', 6, 32)
				if bsStats.App[intd].UserActivity!=nil{
					var counterUserActivity float32
					for _, userActiRec := range bsStats.App[intd].UserActivity{
						counterUserActivity=counterUserActivity+userActiRec.GetCount()
					}
					csvModOutput[intd][73]=strconv.FormatFloat(float64(counterUserActivity),'f', 6, 32)
				}
				//log.Printf("hahahahahaha")
				if bsStats.App[intd].Apk!=nil{
					if bsStats.App[intd].Apk.Service!=nil{
						//log.Printf("muumumuuumuuuhahahahaha")
						var counterServiceLaunches float32=0
						var counterServiceStarts float32=0
						for _, userActRec := range bsStats.App[intd].Apk.Service{
							if userActRec.GetLaunches()!=0{
								counterServiceLaunches=counterServiceLaunches+userActRec.GetLaunches()
							}
							if userActRec.GetStarts()!=0{
								counterServiceStarts=counterServiceStarts+userActRec.GetStarts()
							}
						}

						csvModOutput[intd][74]=strconv.FormatFloat(float64(counterServiceLaunches),'f', 6, 32)
						//log.Printf("what is this bro~ %v",counterServiceStarts)
						//log.Printf("what is this bro yoyo~ %v",counterServiceLaunches)
						csvModOutput[intd][75]=strconv.FormatFloat(float64(counterServiceStarts),'f', 6, 32)
					}
				}

				if bsStats.App[intd].Wakelock!=nil{
					var wlFullCount float32=0
					var wlPartialCount float32=0
					var wlPartialTotalDuration int64=0
					var wlFullTotalDuration int64=0
					var wlWindowCount float32=0
					for _, wlRec := range bsStats.App[intd].Wakelock{
						wlFullCount=wlFullCount+wlRec.GetFullCount()
						wlPartialCount=wlPartialCount+wlRec.GetPartialCount()
						wlPartialTotalDuration=wlPartialTotalDuration+wlRec.GetPartialTotalDurationMsec()
						wlFullTotalDuration=wlFullTotalDuration+wlRec.GetFullTotalDurationMsec()
						wlWindowCount+=wlRec.GetWindowCount()
					}
					csvModOutput[intd][76]=strconv.FormatFloat(float64(wlFullCount),'f', 6, 32)
					csvModOutput[intd][77]=strconv.FormatFloat(float64(wlPartialCount),'f', 6, 32)
					csvModOutput[intd][78]=strconv.FormatFloat(float64(wlPartialTotalDuration),'f', 6, 32)
					csvModOutput[intd][79]=strconv.FormatFloat(float64(wlFullTotalDuration),'f', 6, 32)
					csvModOutput[intd][80]=strconv.FormatFloat(float64(wlWindowCount),'f', 6, 32)
				}
				csvModOutput[intd][81]=strconv.FormatFloat(float64(bsStats.App[intd].Apk.GetWakeups()),'f', 6, 32)
				}


			intd++
		}
		//csvModOutput:= make(map[string]string)
		/////csvModOutput:=map[int][]map[string]string{}
		//csvModOutput[0]["Apk"]=

		file, err :=os.Create(outputDir+"gen1"+fileNameCSV+".csv")
		//
		//if file_is_exists("hoyasa.csv")==true{
		//	file, err= os.Create("ahoyasa.csv")
		//} else {
		//	file, err= os.Create("hoyasa.csv")
		//}


		//file, err := os.Create("hoyasa.csv")
		if err!=nil {
			log.Printf("Cannot create file1", err)
		}
		defer file.Close()




		writer := csv.NewWriter(file)
		defer writer.Flush()
		filedsa:= []string{"Name","CPU_PowerMams","CPU_SystemTimeMs","CPU_UserTimeMs","Foreground_Count","Foreground_TotalTimeMsec",
			"HeadChild_WakeUps","Camera_Count","Camera_TotalTimeMsec","Flashlight_Count","Flashlight_TotalTimeMsec",
			"BluetoothController_IdleTimeMsec", "BluetoothController_PowerMah","BluetoothController_RxTimeMsec",
			"BluetoothMisc_BleScanActualTimeMsec","BluetoothMisc_BleScanCount","BluetoothMisc_BleScanTimeMsec",
			"BluetoothMisc_BleScanCountBg","BluetoothMisc_BleScanResultCount","BluetoothMisc_BleScanActualTimeMsecBg",
			"StateTime_ActiveTimeMsec","StateTime_BackgroundTimeMsec","StateTime_CachedTimeMsec","StateTime_ForegroundServiceTimeMsec",
			"StateTime_ForegroundTimeMsec","StateTime_TopSleepingTimeMsec","StateTime_TopTimeMsec","ModemController_IdleTimeMsec",
			"ModemController_PowerMah","ModemController_RxTimeMsec","Network_BtBytesRx","Network_BtBytesTx","Network_MobileActiveCount",
			"Network_MobileActiveTimeMsec","Network_MobileBytesBgRx","Network_MobileBytesBgTx","Network_MobilePacketsBgRx","Network_MobilePacketsBgTx",
			"Network_MobilePacketsRx","Network_MobilePacketsTx","Network_MobileWakeupCount","Network_BtBytesTx","Network_MobileBytesRx","Network_MobileBytesTx",
			"Network_WifiBytesRx","Network_WifiBytesTx","Network_WifiBytesBgRx","Network_WifiBytesBgTx",
			"Network_WifiPacketsBgRx","Network_WifiPacketsBgTx","Network_WifiPacketsRx","Network_WifiPacketsTx",
			"Network_WifiWakeupCount","Audio_Count","Audio_TotalTimeMsec","Video_Count","Video_TotalTimeMsec",
			"WifiController_IdelTimeMsec","WifiController_PowerMah","WifiController_RxTimeMsec","Wifi_FullWifiLockTimeMsec",
			"Wifi_RxTimeMsec","Wifi_TxTimeMsec","Wifi_IdleTimeMsec","Wifi_RunningTimeMsec","Wifi_ScanCount","Wifi_ScanCountBg",
			"Wifi_ScanTimeMsec","Wifi_ScanActualTimeMsec","Wifi_ScanActualTimeMsecBg","PowerUseItem_ComputerPowerMah",
			"Vibrator_TotalTimeMsec","Vibrator_Count","Count_UserActivity","Count_ServiceLaunches","Count_ServiceStarts","WakeLock_FullCount",
		"WakeLock_PartialCount","WakeLock_PartialTotalDuration","WakeLock_FullTotalDuration","WakeLock_WindowCount","Apk_WakeUps"}
		writer.Write(filedsa)

		writer.WriteAll(csvModOutput)


		///////////////////////////////////////////////////////////////////////////////////



		//log.Println(summariesOutput)

		//log.Println(bsStats.App)

		//eituk kahini :3
		////////////////////////////////////////////////////////////////////////////////////////
		///second csv ekhane

		csvModOutput1 := make([][]string, 10000)
		rowCounter:=0
		appCounter:=0
		for _, appRec := range bsStats.App{
			if appRec != nil{
				if appRec.ScheduledJob != nil{

					for _, appRecSc := range appRec.ScheduledJob{
						csvModOutput1[rowCounter]=make([]string, 10)
						//appRecSc.GetName()
						//appRecSc.GetCount()
						//appRecSc.GetTotalTimeMsec()
						//appRecSc.GetBackgroundTimeMsec()
						//appRecSc.GetBackgroundCount()
						csvModOutput1[rowCounter][0]=appRec.GetName()
						csvModOutput1[rowCounter][1]=appRecSc.GetName()
						csvModOutput1[rowCounter][2]=strconv.FormatFloat(float64(appRecSc.GetCount()),'f', 6, 32)
						csvModOutput1[rowCounter][3]=strconv.FormatFloat(float64(appRecSc.GetBackgroundCount()),'f', 6, 32)
						csvModOutput1[rowCounter][4]=strconv.FormatFloat(float64(appRecSc.GetBackgroundTimeMsec()),'f', 6, 32)
						csvModOutput1[rowCounter][5]=strconv.FormatFloat(float64(appRecSc.GetTotalTimeMsec()),'f', 6, 32)
						rowCounter++
					}
				}
			}
			appCounter++
		}


		//file1, err := os.Create("hoyasa1.csv")
		file1, err :=os.Create(outputDir+"gen2"+fileNameCSV+".csv")


		if err!=nil {
			log.Printf("Cannot create file2", err)
		}
		defer file1.Close()




		writer1 := csv.NewWriter(file1)
		defer writer1.Flush()
		filedsa1:=[]string{
			"App_Name","ScheduledJob_Name","ScheduledJob_Count","ScheduledJob_BackgroundCount","ScheduledJob_BackgroundTimeMsec","ScheduledJob_TotalTimeMsec"}
		writer1.Write(filedsa1)

		writer1.WriteAll(csvModOutput1)




		csvModOutput2 := make([][]string, 10000)
		rowCounter2:=0
		appCounter2:=0
		for _, appRec := range bsStats.App{
			if appRec != nil{
				if appRec.Sensor != nil{

					for _, appRecSc := range appRec.Sensor{
						csvModOutput2[rowCounter2]=make([]string, 10)
						//appRecSc.GetName()
						//appRecSc.GetCount()
						//appRecSc.GetTotalTimeMsec()
						//appRecSc.GetBackgroundTimeMsec()
						//appRecSc.GetBackgroundCount()
						csvModOutput2[rowCounter2][0]=appRec.GetName()
						csvModOutput2[rowCounter2][1]=strconv.FormatFloat(float64(appRecSc.GetTotalTimeMsec()),'f', 6, 32)
						csvModOutput2[rowCounter2][2]=strconv.FormatFloat(float64(appRecSc.GetBackgroundCount()),'f', 6, 32)
						csvModOutput2[rowCounter2][3]=strconv.FormatFloat(float64(appRecSc.GetCount()),'f', 6, 32)
						csvModOutput2[rowCounter2][4]=strconv.FormatFloat(float64(appRecSc.GetActualTimeMsec()),'f', 6, 32)
						csvModOutput2[rowCounter2][5]=strconv.FormatFloat(float64(appRecSc.GetBackgroundActualTimeMsec()),'f', 6, 32)
						csvModOutput2[rowCounter2][6]=strconv.FormatFloat(float64(appRecSc.GetNumber()),'f', 6, 32)
						rowCounter2++
					}
				}
			}
			appCounter2++
		}



		//file2, err := os.Create("hoyasa2.csv")
		file2, err :=os.Create(outputDir+"gen3"+fileNameCSV+".csv")



		if err!=nil {
			log.Printf("Cannot create file3", err)
		}
		defer file2.Close()




		writer2 := csv.NewWriter(file2)
		defer writer2.Flush()
		filedsa2:=[]string{
			"App_Name","SensorTotalTimeMsec","SensorBackgroundCount","SensorCount","SensorActualTimeMsec","SensorBackgroundActualTimeMsec","SensorNumber"}
		writer2.Write(filedsa2)

		writer2.WriteAll(csvModOutput2)



		csvModOutput3 := make([][]string, 10000)
		rowCounter3:=0
		appCounter3:=0
		for _, appRec := range bsStats.App{
			if appRec != nil{
				if appRec.Sync != nil{

					for _, appRecSc := range appRec.Sync{
						csvModOutput3[rowCounter3]=make([]string, 10)
						csvModOutput3[rowCounter3][0]=appRec.GetName()
						csvModOutput3[rowCounter3][1]=appRecSc.GetName()
						csvModOutput3[rowCounter3][2]=strconv.FormatFloat(float64(appRecSc.GetBackgroundCount()),'f', 6, 32)
						csvModOutput3[rowCounter3][3]=strconv.FormatFloat(float64(appRecSc.GetCount()),'f', 6, 32)
						csvModOutput3[rowCounter3][4]=strconv.FormatFloat(float64(appRecSc.GetTotalTimeMsec()),'f', 6, 32)
						csvModOutput3[rowCounter3][5]=strconv.FormatFloat(float64(appRecSc.GetBackgroundTimeMsec()),'f', 6, 32)
						rowCounter3++
					}
				}
			}
			appCounter3++
		}



		//file3, err := os.Create("hoyasa3.csv")
		file3, err :=os.Create(outputDir+"gen4"+fileNameCSV+".csv")

		if err!=nil {
			log.Printf("Cannot create file4", err)
		}
		defer file3.Close()
		writer3 := csv.NewWriter(file3)
		defer writer3.Flush()
		filedsa3:=[]string{
			"App_Name","SyncName","SyncBackgroundCount","SyncCount","SyncTotalTimeMsec","SyncBackgroundTimeMsec"}
		writer3.Write(filedsa3)

		writer3.WriteAll(csvModOutput3)



		csvModOutput4 := make([][]string, 10000)
		rowCounter4:=0
		appCounter4:=0
		for _, appRec := range bsStats.App{
			if appRec != nil{
				if appRec.WakeupAlarm!= nil{

					for _, appRecSc := range appRec.WakeupAlarm{
						csvModOutput4[rowCounter4]=make([]string, 3)
						csvModOutput4[rowCounter4][0]=appRec.GetName()
						csvModOutput4[rowCounter4][1]=appRecSc.GetName()
						csvModOutput4[rowCounter4][2]=strconv.FormatFloat(float64(appRecSc.GetCount()),'f', 6, 32)
						rowCounter4++
					}
				}
			}
			appCounter4++
		}

		//file4, err := os.Create("hoyasa4.csv")
		file4, err :=os.Create(outputDir+"gen5"+fileNameCSV+".csv")

		if err!=nil {
			log.Printf("Cannot create file5", err)
		}
		defer file4.Close()
		writer4 := csv.NewWriter(file4)
		defer writer4.Flush()
		filedsa4:=[]string{
			"App_Name","WakeupAlarmName","WakeupAlarmCount"}
		writer4.Write(filedsa4)

		writer4.WriteAll(csvModOutput4)



		csvModOutput5 := make([][]string, 10000)
		rowCounter5:=0
		appCounter5:=0
		for _, appRec := range bsStats.App{
			if appRec != nil{
				if appRec.UserActivity!= nil{

					for _, appRecSc := range appRec.UserActivity{
						csvModOutput5[rowCounter5]=make([]string, 3)
						csvModOutput5[rowCounter5][0]=appRec.GetName()
						csvModOutput5[rowCounter5][1]=appRecSc.Name.String()
						csvModOutput5[rowCounter5][2]=strconv.FormatFloat(float64(appRecSc.GetCount()),'f', 6, 32)
						rowCounter5++
					}
				}
			}
			appCounter5++
		}

		//file5, err := os.Create("hoyasa5.csv")
		file5, err :=os.Create(outputDir+"gen6"+fileNameCSV+".csv")
		if err!=nil {
			log.Printf("Cannot create file6", err)
		}
		defer file5.Close()
		writer5 := csv.NewWriter(file5)
		defer writer5.Flush()
		filedsa5:=[]string{
			"App_Name","UserActivityName","UserActivityCount"}
		writer5.Write(filedsa5)

		writer5.WriteAll(csvModOutput5)

		//log.Print("iaasdfasdf")
		//log.Printf("ow %v",len(bsStats.App[0].Apk.Service))

		csvModOutput6 := make([][]string, 10000)
		rowCounter6:=0
		appCounter6:=0
		for _, appRec := range bsStats.App{
			if appRec != nil{
				if appRec.Apk!= nil{
					if appRec.Apk.Service !=nil {
						for _, appRecSc := range appRec.Apk.Service {
							csvModOutput6[rowCounter6] = make([]string, 6)
							csvModOutput6[rowCounter6][0] = appRec.GetName()
							csvModOutput6[rowCounter6][1] = appRecSc.GetName()
							csvModOutput6[rowCounter6][2] = strconv.FormatFloat(float64(appRecSc.GetStarts()), 'f', 6, 32)
							csvModOutput6[rowCounter6][3] = strconv.FormatFloat(float64(appRecSc.GetLaunches()), 'f', 6, 32)
							csvModOutput6[rowCounter6][4] = strconv.FormatFloat(float64(appRecSc.GetStartTimeMsec()), 'f', 6, 32)
							rowCounter6++
						}
					}
				}
			}
			appCounter6++
		}

		//file6, err := os.Create("hoyasa6.csv")
		file6, err :=os.Create(outputDir+"gen7"+fileNameCSV+".csv")

		if err!=nil {
			log.Printf("Cannot create file7", err)
		}
		defer file6.Close()

		writer6 := csv.NewWriter(file6)
		defer writer6.Flush()
		filedsa6:=[]string{
			"App_Name","ServiceName","ServiceStarts","ServiceLaunches","ServiceStartTimeMsec"}
		writer6.Write(filedsa6)

		writer6.WriteAll(csvModOutput6)



		/////////////////////////////////////////////////////////////////////
		////Appedned Block by Kanak Ends

		warnings = append(warnings, activityManagerOutput.Warnings...)
		fn := late.fileName
		if diff {
			fn = fmt.Sprintf("%s - %s", earl.fileName, late.fileName)
		}
		data := presenter.Data(late.meta, fn,
			summariesOutput.summaries,
			bsStats, historianOutput.html,
			warnings,
			errs, summariesOutput.overflowMs > 0, true)

		historianV2Logs := []historianV2Log{
			{
				Source: batteryHistory,
				CSV:    summariesOutput.historianV2CSV,
			},
			{
				Source: wearableLog,
				CSV:    wearableOutput,
			},
			{
				Source:  kernelDmesg,
				CSV:     dmesgOutput.CSV,
				StartMs: dmesgOutput.StartMs,
			},
			{
				Source: broadcastsLog,
				CSV:    broadcastsOutput.csv,
			},
		}
		for s, l := range activityManagerOutput.Logs {
			if l == nil {
				log.Print("Nil logcat log received")
				continue
			}
			source := ""
			switch s {
			case activity.EventLogSection:
				source = eventLog
			case activity.SystemLogSection:
				source = systemLog
			case activity.LastLogcatSection:
				source = lastLogcat
			default:
				log.Printf("Logcat section %q not handled", s)
				// Show it anyway.
				source = s
			}
			historianV2Logs = append(historianV2Logs, historianV2Log{
				Source:  source,
				CSV:     l.CSV,
				StartMs: l.StartMs,
			})
		}

		var note string
		if diff {
			note = "Only the System and App Stats tabs show the delta between the first and second bug reports."
		}
		pd.responseArr = append(pd.responseArr, uploadResponse{
			SDKVersion:      data.SDKVersion,
			HistorianV2Logs: historianV2Logs,
			LevelSummaryCSV: summariesOutput.levelSummaryCSV,
			ReportVersion:   data.CheckinSummary.ReportVersion,
			AppStats:        data.AppStats,
			BatteryStats:    bsStats,
			DeviceCapacity:  bsStats.GetSystem().GetPowerUseSummary().GetBatteryCapacityMah(),
			HistogramStats:  extractHistogramStats(data),
			TimeToDelta:     summariesOutput.timeToDelta,
			CriticalError:   ce,
			Note:            note,
			FileName:        data.Filename,
			Location:        late.dt.Location().String(),
			OverflowMs:      summariesOutput.overflowMs,
			IsDiff:          diff,
		})
		pd.data = append(pd.data, data)

		if diff {
			log.Printf("Trace finished diffing files.")
		} else {
			log.Printf("Trace finished analyzing %q file.", brDA.fileName)
		}
	}

	newBrData := func(fName, contents string) (*brData, error) {
		if fName == "" || contents == "" {
			return nil, nil
		}
		br := brData{fileName: fName, contents: contents}
		var err error
		br.meta, err = bugreportutils.ParseMetaInfo(contents)
		if err != nil {
			// If there are issues getting the meta info, then the file is most likely not a bug report.
			return nil, errors.New("error parsing the bug report. Please provide a well formed bug report")
		}
		var errs []error
		br.bt, errs = batteryTime(contents)
		if len(errs) > 0 {
			log.Printf("failed to extract battery info: %s", historianutils.ErrorsToString(errs))
			// It's fine to continue if this fails.
		}
		br.dt, err = bugreportutils.DumpState(contents)
		if err != nil {
			log.Printf("failed to extract time information from bugreport dumpstate: %v", err)
		}
		return &br, nil
	}

	brA, err := newBrData(fnameA, contentsA)
	if err != nil {
		return err
	}
	brB, err := newBrData(fnameB, contentsB)
	if err != nil {
		return err
	}
	doParsing(brA, brB)

	return nil
}

func analyze(bugReport string, pkgs []*usagepb.PackageInfo) summariesData {
	upm, errs := parseutils.UIDAndPackageNameMapping(bugReport, pkgs)

	var bufTotal, bufLevel bytes.Buffer
	// repTotal contains summaries over discharge intervals
	repTotal := parseutils.AnalyzeHistory(&bufTotal, bugReport, parseutils.FormatTotalTime, upm, false)
	// repLevel contains summaries for each battery level drop.
	// The generated errors would be the exact same as repTotal.Errs so no need to track or add them again.
	parseutils.AnalyzeHistory(&bufLevel, bugReport, parseutils.FormatBatteryLevel, upm, false)

	// Exclude summaries with no change in battery level
	var summariesTotal []parseutils.ActivitySummary
	for _, s := range repTotal.Summaries {
		if s.InitialBatteryLevel != s.FinalBatteryLevel {
			summariesTotal = append(summariesTotal, s)
		}
	}

	errs = append(errs, repTotal.Errs...)
	return summariesData{summariesTotal, bufTotal.String(), bufLevel.String(), repTotal.TimeToDelta, errs, repTotal.OverflowMs}
}

// generateHistorianPlot calls the Historian python script to generate html charts.
func generateHistorianPlot(reportName, filepath string) (string, error) {
	return historianutils.RunCommand("python", scriptsPath(scriptsDir, "historian.py"), "-c", "-m", "-r", reportName, filepath)
}

// generateKernelCSV calls the python script to convert kernel trace files into a CSV format parseable by kernel.Parse.
func generateKernelCSV(bugReportPath, tracePath, model string) (string, error) {
	return historianutils.RunCommand("python", scriptsPath(scriptsDir, "kernel_trace.py"), "--bugreport", bugReportPath, "--trace", tracePath, "--device", model)
}

// batteryTime extracts the battery time info from a bug report.
func batteryTime(contents string) (*bspb.BatteryStats_System_Battery, []error) {
	for _, line := range strings.Split(contents, "\n") {
		if m, result := historianutils.SubexpNames(batteryRE, line); m {
			s := &bspb.BatteryStats_System{}
			record := strings.Split(result["batteryTime"], ",")
			_, errs := checkinparse.SystemBattery(&checkinutil.PrefixCounter{}, record, s)
			if len(errs) > 0 {
				return nil, errs
			}
			return s.GetBattery(), nil
		}
	}
	return nil, []error{errors.New("could not find battery time info in bugreport")}
}
































