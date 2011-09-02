CMOS = util.cmo p.cmo r5rsds.cmo schemeParser.cmo
MAIN = main.ml
OCAMLC = ocamlc
TARGET = repl

.PHONY: clean
.SUFFIXES: .cmo .ml

$(TARGET): $(CMOS)
	$(OCAMLC) -o $(TARGET) $(CMOS) $(MAIN)

.ml.cmo:
	$(OCAMLC) -c $<

p.cmo: util.cmo
schemeParser.cmo: p.cmo util.cmo r5rsds.cmo

clean:
	rm -f $(TARGET) *.cmo *.cmi *.cmx *.o
