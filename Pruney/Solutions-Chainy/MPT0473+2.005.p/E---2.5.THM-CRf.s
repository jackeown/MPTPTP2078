%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:21 EST 2020

% Result     : Theorem 0.16s
% Output     : CNFRefutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   16 (  49 expanded)
%              Number of clauses        :   10 (  18 expanded)
%              Number of leaves         :    3 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 ( 152 expanded)
%              Number of equality atoms :   30 ( 110 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( k1_relat_1(X1) = k1_xboole_0
        <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t65_relat_1])).

fof(c_0_4,plain,(
    ! [X2] :
      ( ( k1_relat_1(X2) != k1_xboole_0
        | X2 = k1_xboole_0
        | ~ v1_relat_1(X2) )
      & ( k2_relat_1(X2) != k1_xboole_0
        | X2 = k1_xboole_0
        | ~ v1_relat_1(X2) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

fof(c_0_5,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & ( k1_relat_1(esk1_0) != k1_xboole_0
      | k2_relat_1(esk1_0) != k1_xboole_0 )
    & ( k1_relat_1(esk1_0) = k1_xboole_0
      | k2_relat_1(esk1_0) = k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_6,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( k1_relat_1(esk1_0) = k1_xboole_0
    | k2_relat_1(esk1_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,negated_conjecture,
    ( k1_relat_1(esk1_0) = k1_xboole_0
    | esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8])])).

cnf(c_0_11,negated_conjecture,
    ( k1_relat_1(esk1_0) != k1_xboole_0
    | k2_relat_1(esk1_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_8])])).

cnf(c_0_13,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_14,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_15,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_12]),c_0_14])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.31  % Computer   : n010.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 14:28:14 EST 2020
% 0.16/0.31  % CPUTime    : 
% 0.16/0.31  # Version: 2.5pre002
% 0.16/0.32  # No SInE strategy applied
% 0.16/0.32  # Trying AutoSched0 for 299 seconds
% 0.16/0.34  # AutoSched0-Mode selected heuristic G_____0026_C18_F1_SE_CS_SP_S4S
% 0.16/0.34  # and selection function SelectNewComplexAHPNS.
% 0.16/0.34  #
% 0.16/0.34  # Preprocessing time       : 0.026 s
% 0.16/0.34  
% 0.16/0.34  # Proof found!
% 0.16/0.34  # SZS status Theorem
% 0.16/0.34  # SZS output start CNFRefutation
% 0.16/0.34  fof(t65_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 0.16/0.34  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 0.16/0.34  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.16/0.34  fof(c_0_3, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t65_relat_1])).
% 0.16/0.34  fof(c_0_4, plain, ![X2]:((k1_relat_1(X2)!=k1_xboole_0|X2=k1_xboole_0|~v1_relat_1(X2))&(k2_relat_1(X2)!=k1_xboole_0|X2=k1_xboole_0|~v1_relat_1(X2))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.16/0.34  fof(c_0_5, negated_conjecture, (v1_relat_1(esk1_0)&((k1_relat_1(esk1_0)!=k1_xboole_0|k2_relat_1(esk1_0)!=k1_xboole_0)&(k1_relat_1(esk1_0)=k1_xboole_0|k2_relat_1(esk1_0)=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.16/0.34  cnf(c_0_6, plain, (X1=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.16/0.34  cnf(c_0_7, negated_conjecture, (k1_relat_1(esk1_0)=k1_xboole_0|k2_relat_1(esk1_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.16/0.34  cnf(c_0_8, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.16/0.34  cnf(c_0_9, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.16/0.34  cnf(c_0_10, negated_conjecture, (k1_relat_1(esk1_0)=k1_xboole_0|esk1_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6, c_0_7]), c_0_8])])).
% 0.16/0.34  cnf(c_0_11, negated_conjecture, (k1_relat_1(esk1_0)!=k1_xboole_0|k2_relat_1(esk1_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.16/0.34  cnf(c_0_12, negated_conjecture, (esk1_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_8])])).
% 0.16/0.34  cnf(c_0_13, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.16/0.34  cnf(c_0_14, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.16/0.34  cnf(c_0_15, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11, c_0_12]), c_0_13]), c_0_12]), c_0_14])]), ['proof']).
% 0.16/0.34  # SZS output end CNFRefutation
% 0.16/0.34  # Proof object total steps             : 16
% 0.16/0.34  # Proof object clause steps            : 10
% 0.16/0.34  # Proof object formula steps           : 6
% 0.16/0.34  # Proof object conjectures             : 9
% 0.16/0.34  # Proof object clause conjectures      : 6
% 0.16/0.34  # Proof object formula conjectures     : 3
% 0.16/0.34  # Proof object initial clauses used    : 7
% 0.16/0.34  # Proof object initial formulas used   : 3
% 0.16/0.34  # Proof object generating inferences   : 2
% 0.16/0.34  # Proof object simplifying inferences  : 9
% 0.16/0.34  # Training examples: 0 positive, 0 negative
% 0.16/0.34  # Parsed axioms                        : 3
% 0.16/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.16/0.34  # Initial clauses                      : 7
% 0.16/0.34  # Removed in clause preprocessing      : 0
% 0.16/0.34  # Initial clauses in saturation        : 7
% 0.16/0.34  # Processed clauses                    : 9
% 0.16/0.34  # ...of these trivial                  : 0
% 0.16/0.34  # ...subsumed                          : 0
% 0.16/0.34  # ...remaining for further processing  : 9
% 0.16/0.34  # Other redundant clauses eliminated   : 0
% 0.16/0.34  # Clauses deleted for lack of memory   : 0
% 0.16/0.34  # Backward-subsumed                    : 0
% 0.16/0.34  # Backward-rewritten                   : 4
% 0.16/0.34  # Generated clauses                    : 3
% 0.16/0.34  # ...of the previous two non-trivial   : 3
% 0.16/0.34  # Contextual simplify-reflections      : 0
% 0.16/0.34  # Paramodulations                      : 3
% 0.16/0.34  # Factorizations                       : 0
% 0.16/0.34  # Equation resolutions                 : 0
% 0.16/0.34  # Propositional unsat checks           : 0
% 0.16/0.34  #    Propositional check models        : 0
% 0.16/0.34  #    Propositional check unsatisfiable : 0
% 0.16/0.34  #    Propositional clauses             : 0
% 0.16/0.34  #    Propositional clauses after purity: 0
% 0.16/0.34  #    Propositional unsat core size     : 0
% 0.16/0.34  #    Propositional preprocessing time  : 0.000
% 0.16/0.34  #    Propositional encoding time       : 0.000
% 0.16/0.34  #    Propositional solver time         : 0.000
% 0.16/0.34  #    Success case prop preproc time    : 0.000
% 0.16/0.34  #    Success case prop encoding time   : 0.000
% 0.16/0.34  #    Success case prop solver time     : 0.000
% 0.16/0.34  # Current number of processed clauses  : 5
% 0.16/0.34  #    Positive orientable unit clauses  : 3
% 0.16/0.34  #    Positive unorientable unit clauses: 0
% 0.16/0.34  #    Negative unit clauses             : 0
% 0.16/0.34  #    Non-unit-clauses                  : 2
% 0.16/0.34  # Current number of unprocessed clauses: 1
% 0.16/0.34  # ...number of literals in the above   : 2
% 0.16/0.34  # Current number of archived formulas  : 0
% 0.16/0.34  # Current number of archived clauses   : 4
% 0.16/0.34  # Clause-clause subsumption calls (NU) : 1
% 0.16/0.34  # Rec. Clause-clause subsumption calls : 1
% 0.16/0.34  # Non-unit clause-clause subsumptions  : 0
% 0.16/0.34  # Unit Clause-clause subsumption calls : 0
% 0.16/0.34  # Rewrite failures with RHS unbound    : 0
% 0.16/0.34  # BW rewrite match attempts            : 1
% 0.16/0.34  # BW rewrite match successes           : 1
% 0.16/0.34  # Condensation attempts                : 0
% 0.16/0.34  # Condensation successes               : 0
% 0.16/0.34  # Termbank termtop insertions          : 352
% 0.16/0.34  
% 0.16/0.34  # -------------------------------------------------
% 0.16/0.34  # User time                : 0.024 s
% 0.16/0.34  # System time              : 0.005 s
% 0.16/0.34  # Total time               : 0.029 s
% 0.16/0.34  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
