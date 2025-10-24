# a massive hack
cp widget/src/tacticSuggestionPanel.tsx .lake/packages/proofwidgets/widget/src/
cd .lake/packages/proofwidgets 
lake build widgetJsAll
cd ../../../
cp .lake/packages/proofwidgets/widget/dist/tacticSuggestionPanel.js ./widget/dist/