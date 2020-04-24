ISABELLE=/usr/local/bin/isabelle2020

browser_info:
# 	rm -fr src/ROOT
# 	cd src && isabelle mkroot .
# 	sed -i -e 's/src/Hygge_Theory/g' src/ROOT
# 	sed -i -e 's/(\* Baz \*)/Hygge_Theory/g' src/ROOT
# 	sed -i -e 's/+/\
# +  description {* Denotational and operational semantics for TESL *}/g' src/ROOT
	cd src && $(ISABELLE) build -c -d . -o browser_info -v TESL
	mv "`$(ISABELLE) getenv -b ISABELLE_BROWSER_INFO`/Unsorted/TESL" .
	cp docs/FirstExample.png TESL/
	rm -fr docs
	mv TESL docs
	sed -i -e 's/Session/Library/g' docs/index.html
	sed -i -e 's/<h2>Theories<\/h2>/<h2><a href="session_graph.pdf">Index<\/a><\/h2>/g' docs/index.html
	sed -i -e 's/<p>View <a href="session_graph.pdf">theory dependencies<\/a><\/p>/<p>Denotational and operational semantics for the <a href="http:\/\/wdi.supelec.fr\/software\/TESL\/">Tagged Events Specification Language<\/a>.<\/p>\
<p>Check out root theory <a href="Hygge_Theory.html">Hygge_Theory<\/a> for soundness, completeness, progress and termination properties, and <a href="Stuttering.html">Stuttering<\/a> for stuttering properties.<\/p>/g' docs/index.html
	sed -i -e 's/<\/body>/<p>Copyright (c) 2017-2019 T. Balabonski, F. Boulanger, C. Keller, H. Nguyen Van, B. Valiron, B. Wolff, CentraleSupélec \/ Université Paris-Sud \/ CNRS<\/p>\
<\/body>/g' docs/index.html
	sed -i -e 's/..\/..\/HOL\/HOL\//http:\/\/isabelle.in.tum.de\/website-Isabelle2019\/dist\/library\/HOL\/HOL\//g' docs/TESL.html

pdf_document:
# 	rm -fr src/ROOT src/document
# 	cd src && $ISABELLE mkroot -d .
# 	sed -i -e 's/src/Hygge_Theory/g' src/ROOT
# 	sed -i -e 's/(\* Baz \*)/Hygge_Theory/g' src/ROOT
# 	sed -i -e 's/+/\
# +  description {* Denotational and operational semantics for TESL *}/g' src/ROOT
	cd src && $(ISABELLE) build -D .
