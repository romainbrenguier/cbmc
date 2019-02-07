#!/usr/bin/env node
// To install commander run: `npm install --save commander`
// Add PROFILE_BREAKPOINT macros in cbmc code, run with verbosity 0 and give
// the output to this script to get a report.
// For example add `PROFILER_BREAKPOINT` at two different position of a,
// function, and include `util/profiler.h` in the file, recompile the code,
// run `cbmc some_test.c --verbosity 0 >profile.out`. Then run this script:
// `scripts/profiling_report.js profile.out`. This will output a table where
// the entry for [a][b] corresponds to the time spent between a and b.

let program = require('commander');

program
    .arguments('<file>')
    .option('-j, --json', 'Output as json rather than javascript')
    .option('-d, --dot', 'Output as dot')
    .action(function (file) {
        let lineReader = require('readline').createInterface({
            input: require('fs').createReadStream(file)
        });
        let map = {};
        let lastPosition = "program start";
        lineReader.on('line', function (data) {
            const separatorPosition = data.indexOf(" ");
            const newPosition = data.substr(0, separatorPosition);
            const time = parseFloat(data.substr(separatorPosition + 1));
            if (typeof map[lastPosition] == 'undefined')
                map[lastPosition] = {};
            const mapEntry = map[lastPosition][newPosition];
            if (typeof mapEntry != 'undefined')
                map[lastPosition][newPosition] = mapEntry + time;
            else
                map[lastPosition][newPosition] = time;
            lastPosition = newPosition;
        });

        lineReader.on('close', function () {
            if (typeof program.json != 'undefined')
                console.log(JSON.stringify(map));
            else if (typeof program.dot != 'undefined') {
                let total = 0.0;
                for (let [key, value] of Object.entries(map)) {
                    for (let [newKey, time] of Object.entries(value))
                        total += time;
                }
                console.log("digraph profile {");
                for (let [key, value] of Object.entries(map)) {
                    for (let [newKey, time] of Object.entries(value)) {
                        const color = ""; // (time > 1) ? "color=red," : "";
                        const width = "penwidth=" + (5 * (time / (total+0.1)) + 0.1).toFixed(3) + ",";
                        const percentage = (100 * time / (total+0.1)).toFixed(6);
                        console.log("  \"" + key + "\" -> \"" + newKey + "\" ["
                            + width + color + "label=\"" + time.toFixed(6) + "s " 
                            + percentage + "%\"];");
                    }
                }
                console.log("}");
            } else {
                console.log(map);
            }
        });
    })
    .parse(process.argv);
