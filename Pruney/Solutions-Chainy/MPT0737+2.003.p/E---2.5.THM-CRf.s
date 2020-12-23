%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:10 EST 2020

% Result     : Theorem 0.08s
% Output     : CNFRefutation 0.08s
% Verified   : 
% Statistics : Number of formulae       :   27 (  45 expanded)
%              Number of clauses        :   14 (  17 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :    7
%              Number of atoms          :   82 ( 142 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(t25_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => r3_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_ordinal1)).

fof(d9_xboole_0,axiom,(
    ! [X1,X2] :
      ( r3_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        | r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).

fof(reflexivity_r3_xboole_0,axiom,(
    ! [X1,X2] : r3_xboole_0(X1,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_xboole_0)).

fof(c_0_6,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_ordinal1(X7)
        | ~ r2_hidden(X8,X7)
        | r1_tarski(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_ordinal1(X9) )
      & ( ~ r1_tarski(esk1_1(X9),X9)
        | v1_ordinal1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

fof(c_0_7,plain,(
    ! [X11,X12] :
      ( ~ v3_ordinal1(X11)
      | ~ v3_ordinal1(X12)
      | r2_hidden(X11,X12)
      | X11 = X12
      | r2_hidden(X12,X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

fof(c_0_8,plain,(
    ! [X6] :
      ( ( v1_ordinal1(X6)
        | ~ v3_ordinal1(X6) )
      & ( v2_ordinal1(X6)
        | ~ v3_ordinal1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

cnf(c_0_9,plain,
    ( r1_tarski(X2,X1)
    | ~ v1_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => r3_xboole_0(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t25_ordinal1])).

fof(c_0_13,plain,(
    ! [X3,X4] :
      ( ( ~ r3_xboole_0(X3,X4)
        | r1_tarski(X3,X4)
        | r1_tarski(X4,X3) )
      & ( ~ r1_tarski(X3,X4)
        | r3_xboole_0(X3,X4) )
      & ( ~ r1_tarski(X4,X3)
        | r3_xboole_0(X3,X4) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_xboole_0])])])).

cnf(c_0_14,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | r1_tarski(X2,X1)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])).

fof(c_0_15,negated_conjecture,
    ( v3_ordinal1(esk2_0)
    & v3_ordinal1(esk3_0)
    & ~ r3_xboole_0(esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_16,plain,
    ( r3_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( X1 = X2
    | r1_tarski(X2,X1)
    | r1_tarski(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_14]),c_0_11])).

cnf(c_0_18,plain,
    ( r3_xboole_0(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( ~ r3_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( X1 = X2
    | r3_xboole_0(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( v3_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( v3_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,plain,(
    ! [X5] : r3_xboole_0(X5,X5) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_xboole_0])])).

cnf(c_0_24,negated_conjecture,
    ( esk2_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])])).

cnf(c_0_25,plain,
    ( r3_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_24]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.09  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.08/0.28  % Computer   : n003.cluster.edu
% 0.08/0.28  % Model      : x86_64 x86_64
% 0.08/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.28  % Memory     : 8042.1875MB
% 0.08/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.28  % CPULimit   : 60
% 0.08/0.28  % WCLimit    : 600
% 0.08/0.28  % DateTime   : Tue Dec  1 10:17:57 EST 2020
% 0.08/0.28  % CPUTime    : 
% 0.08/0.28  # Version: 2.5pre002
% 0.08/0.28  # No SInE strategy applied
% 0.08/0.28  # Trying AutoSched0 for 299 seconds
% 0.08/0.30  # AutoSched0-Mode selected heuristic G_____0026_C18_F1_SE_CS_SP_S4S
% 0.08/0.30  # and selection function SelectNewComplexAHPNS.
% 0.08/0.30  #
% 0.08/0.30  # Preprocessing time       : 0.012 s
% 0.08/0.30  
% 0.08/0.30  # Proof found!
% 0.08/0.30  # SZS status Theorem
% 0.08/0.30  # SZS output start CNFRefutation
% 0.08/0.30  fof(d2_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)<=>![X2]:(r2_hidden(X2,X1)=>r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 0.08/0.30  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 0.08/0.30  fof(cc1_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(v1_ordinal1(X1)&v2_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 0.08/0.30  fof(t25_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>r3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_ordinal1)).
% 0.08/0.30  fof(d9_xboole_0, axiom, ![X1, X2]:(r3_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)|r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_xboole_0)).
% 0.08/0.30  fof(reflexivity_r3_xboole_0, axiom, ![X1, X2]:r3_xboole_0(X1,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r3_xboole_0)).
% 0.08/0.30  fof(c_0_6, plain, ![X7, X8, X9]:((~v1_ordinal1(X7)|(~r2_hidden(X8,X7)|r1_tarski(X8,X7)))&((r2_hidden(esk1_1(X9),X9)|v1_ordinal1(X9))&(~r1_tarski(esk1_1(X9),X9)|v1_ordinal1(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).
% 0.08/0.30  fof(c_0_7, plain, ![X11, X12]:(~v3_ordinal1(X11)|(~v3_ordinal1(X12)|(r2_hidden(X11,X12)|X11=X12|r2_hidden(X12,X11)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 0.08/0.30  fof(c_0_8, plain, ![X6]:((v1_ordinal1(X6)|~v3_ordinal1(X6))&(v2_ordinal1(X6)|~v3_ordinal1(X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).
% 0.08/0.30  cnf(c_0_9, plain, (r1_tarski(X2,X1)|~v1_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.08/0.30  cnf(c_0_10, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.08/0.30  cnf(c_0_11, plain, (v1_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.08/0.30  fof(c_0_12, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>r3_xboole_0(X1,X2)))), inference(assume_negation,[status(cth)],[t25_ordinal1])).
% 0.08/0.30  fof(c_0_13, plain, ![X3, X4]:((~r3_xboole_0(X3,X4)|(r1_tarski(X3,X4)|r1_tarski(X4,X3)))&((~r1_tarski(X3,X4)|r3_xboole_0(X3,X4))&(~r1_tarski(X4,X3)|r3_xboole_0(X3,X4)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_xboole_0])])])).
% 0.08/0.30  cnf(c_0_14, plain, (X1=X2|r2_hidden(X1,X2)|r1_tarski(X2,X1)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11])).
% 0.08/0.30  fof(c_0_15, negated_conjecture, (v3_ordinal1(esk2_0)&(v3_ordinal1(esk3_0)&~r3_xboole_0(esk2_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.08/0.30  cnf(c_0_16, plain, (r3_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.08/0.30  cnf(c_0_17, plain, (X1=X2|r1_tarski(X2,X1)|r1_tarski(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_14]), c_0_11])).
% 0.08/0.30  cnf(c_0_18, plain, (r3_xboole_0(X2,X1)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.08/0.30  cnf(c_0_19, negated_conjecture, (~r3_xboole_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.08/0.30  cnf(c_0_20, plain, (X1=X2|r3_xboole_0(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.08/0.30  cnf(c_0_21, negated_conjecture, (v3_ordinal1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.08/0.30  cnf(c_0_22, negated_conjecture, (v3_ordinal1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.08/0.30  fof(c_0_23, plain, ![X5]:r3_xboole_0(X5,X5), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_xboole_0])])).
% 0.08/0.30  cnf(c_0_24, negated_conjecture, (esk2_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])])).
% 0.08/0.30  cnf(c_0_25, plain, (r3_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.08/0.30  cnf(c_0_26, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_24]), c_0_25])]), ['proof']).
% 0.08/0.30  # SZS output end CNFRefutation
% 0.08/0.30  # Proof object total steps             : 27
% 0.08/0.30  # Proof object clause steps            : 14
% 0.08/0.30  # Proof object formula steps           : 13
% 0.08/0.30  # Proof object conjectures             : 8
% 0.08/0.30  # Proof object clause conjectures      : 5
% 0.08/0.30  # Proof object formula conjectures     : 3
% 0.08/0.30  # Proof object initial clauses used    : 9
% 0.08/0.30  # Proof object initial formulas used   : 6
% 0.08/0.30  # Proof object generating inferences   : 4
% 0.08/0.30  # Proof object simplifying inferences  : 9
% 0.08/0.30  # Training examples: 0 positive, 0 negative
% 0.08/0.30  # Parsed axioms                        : 6
% 0.08/0.30  # Removed by relevancy pruning/SinE    : 0
% 0.08/0.30  # Initial clauses                      : 13
% 0.08/0.30  # Removed in clause preprocessing      : 0
% 0.08/0.30  # Initial clauses in saturation        : 13
% 0.08/0.30  # Processed clauses                    : 19
% 0.08/0.30  # ...of these trivial                  : 0
% 0.08/0.30  # ...subsumed                          : 1
% 0.08/0.30  # ...remaining for further processing  : 18
% 0.08/0.30  # Other redundant clauses eliminated   : 0
% 0.08/0.30  # Clauses deleted for lack of memory   : 0
% 0.08/0.30  # Backward-subsumed                    : 0
% 0.08/0.30  # Backward-rewritten                   : 2
% 0.08/0.30  # Generated clauses                    : 19
% 0.08/0.30  # ...of the previous two non-trivial   : 12
% 0.08/0.30  # Contextual simplify-reflections      : 3
% 0.08/0.30  # Paramodulations                      : 15
% 0.08/0.30  # Factorizations                       : 4
% 0.08/0.30  # Equation resolutions                 : 0
% 0.08/0.30  # Propositional unsat checks           : 0
% 0.08/0.30  #    Propositional check models        : 0
% 0.08/0.30  #    Propositional check unsatisfiable : 0
% 0.08/0.30  #    Propositional clauses             : 0
% 0.08/0.30  #    Propositional clauses after purity: 0
% 0.08/0.30  #    Propositional unsat core size     : 0
% 0.08/0.30  #    Propositional preprocessing time  : 0.000
% 0.08/0.30  #    Propositional encoding time       : 0.000
% 0.08/0.30  #    Propositional solver time         : 0.000
% 0.08/0.30  #    Success case prop preproc time    : 0.000
% 0.08/0.30  #    Success case prop encoding time   : 0.000
% 0.08/0.30  #    Success case prop solver time     : 0.000
% 0.08/0.30  # Current number of processed clauses  : 16
% 0.08/0.30  #    Positive orientable unit clauses  : 4
% 0.08/0.30  #    Positive unorientable unit clauses: 0
% 0.08/0.30  #    Negative unit clauses             : 0
% 0.08/0.30  #    Non-unit-clauses                  : 12
% 0.08/0.30  # Current number of unprocessed clauses: 6
% 0.08/0.30  # ...number of literals in the above   : 30
% 0.08/0.30  # Current number of archived formulas  : 0
% 0.08/0.30  # Current number of archived clauses   : 2
% 0.08/0.30  # Clause-clause subsumption calls (NU) : 11
% 0.08/0.30  # Rec. Clause-clause subsumption calls : 7
% 0.08/0.30  # Non-unit clause-clause subsumptions  : 4
% 0.08/0.30  # Unit Clause-clause subsumption calls : 3
% 0.08/0.30  # Rewrite failures with RHS unbound    : 0
% 0.08/0.30  # BW rewrite match attempts            : 4
% 0.08/0.30  # BW rewrite match successes           : 1
% 0.08/0.30  # Condensation attempts                : 0
% 0.08/0.30  # Condensation successes               : 0
% 0.08/0.30  # Termbank termtop insertions          : 865
% 0.08/0.30  
% 0.08/0.30  # -------------------------------------------------
% 0.08/0.30  # User time                : 0.012 s
% 0.08/0.30  # System time              : 0.003 s
% 0.08/0.30  # Total time               : 0.015 s
% 0.08/0.30  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
