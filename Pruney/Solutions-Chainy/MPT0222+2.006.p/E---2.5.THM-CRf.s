%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:37:46 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   20 (  32 expanded)
%              Number of clauses        :   11 (  14 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  60 expanded)
%              Number of equality atoms :   22 (  34 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( X1 != X2
     => r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t87_enumset1,axiom,(
    ! [X1] : k3_enumset1(X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_enumset1)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( X1 != X2
       => r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ) ),
    inference(assume_negation,[status(cth)],[t17_zfmisc_1])).

fof(c_0_5,plain,(
    ! [X4,X5,X6,X7,X8,X9] :
      ( ( ~ r2_hidden(X6,X5)
        | X6 = X4
        | X5 != k1_tarski(X4) )
      & ( X7 != X4
        | r2_hidden(X7,X5)
        | X5 != k1_tarski(X4) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | esk1_2(X8,X9) != X8
        | X9 = k1_tarski(X8) )
      & ( r2_hidden(esk1_2(X8,X9),X9)
        | esk1_2(X8,X9) = X8
        | X9 = k1_tarski(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_6,plain,(
    ! [X11] : k3_enumset1(X11,X11,X11,X11,X11) = k1_tarski(X11) ),
    inference(variable_rename,[status(thm)],[t87_enumset1])).

fof(c_0_7,negated_conjecture,
    ( esk2_0 != esk3_0
    & ~ r1_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_8,plain,(
    ! [X15,X16] :
      ( r2_hidden(X15,X16)
      | r1_xboole_0(k1_tarski(X15),X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

cnf(c_0_9,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( k3_enumset1(X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( ~ r1_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( ~ r1_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_10]),c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[c_0_12,c_0_10])).

cnf(c_0_16,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk2_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.32  % Computer   : n012.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:44:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.13/0.34  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.34  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.34  #
% 0.13/0.34  # Preprocessing time       : 0.014 s
% 0.13/0.34  # Presaturation interreduction done
% 0.13/0.34  
% 0.13/0.34  # Proof found!
% 0.13/0.34  # SZS status Theorem
% 0.13/0.34  # SZS output start CNFRefutation
% 0.13/0.34  fof(t17_zfmisc_1, conjecture, ![X1, X2]:(X1!=X2=>r1_xboole_0(k1_tarski(X1),k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 0.13/0.34  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.13/0.34  fof(t87_enumset1, axiom, ![X1]:k3_enumset1(X1,X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_enumset1)).
% 0.13/0.34  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.13/0.34  fof(c_0_4, negated_conjecture, ~(![X1, X2]:(X1!=X2=>r1_xboole_0(k1_tarski(X1),k1_tarski(X2)))), inference(assume_negation,[status(cth)],[t17_zfmisc_1])).
% 0.13/0.34  fof(c_0_5, plain, ![X4, X5, X6, X7, X8, X9]:(((~r2_hidden(X6,X5)|X6=X4|X5!=k1_tarski(X4))&(X7!=X4|r2_hidden(X7,X5)|X5!=k1_tarski(X4)))&((~r2_hidden(esk1_2(X8,X9),X9)|esk1_2(X8,X9)!=X8|X9=k1_tarski(X8))&(r2_hidden(esk1_2(X8,X9),X9)|esk1_2(X8,X9)=X8|X9=k1_tarski(X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.13/0.34  fof(c_0_6, plain, ![X11]:k3_enumset1(X11,X11,X11,X11,X11)=k1_tarski(X11), inference(variable_rename,[status(thm)],[t87_enumset1])).
% 0.13/0.34  fof(c_0_7, negated_conjecture, (esk2_0!=esk3_0&~r1_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.13/0.34  fof(c_0_8, plain, ![X15, X16]:(r2_hidden(X15,X16)|r1_xboole_0(k1_tarski(X15),X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.13/0.34  cnf(c_0_9, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.34  cnf(c_0_10, plain, (k3_enumset1(X1,X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.34  cnf(c_0_11, negated_conjecture, (~r1_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.34  cnf(c_0_12, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.34  cnf(c_0_13, plain, (X1=X3|X2!=k3_enumset1(X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_9, c_0_10])).
% 0.13/0.34  cnf(c_0_14, negated_conjecture, (~r1_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11, c_0_10]), c_0_10])).
% 0.13/0.34  cnf(c_0_15, plain, (r2_hidden(X1,X2)|r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[c_0_12, c_0_10])).
% 0.13/0.34  cnf(c_0_16, plain, (X1=X2|~r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_13])).
% 0.13/0.34  cnf(c_0_17, negated_conjecture, (r2_hidden(esk2_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.34  cnf(c_0_18, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.34  cnf(c_0_19, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), ['proof']).
% 0.13/0.34  # SZS output end CNFRefutation
% 0.13/0.34  # Proof object total steps             : 20
% 0.13/0.34  # Proof object clause steps            : 11
% 0.13/0.34  # Proof object formula steps           : 9
% 0.13/0.34  # Proof object conjectures             : 8
% 0.13/0.34  # Proof object clause conjectures      : 5
% 0.13/0.34  # Proof object formula conjectures     : 3
% 0.13/0.34  # Proof object initial clauses used    : 5
% 0.13/0.34  # Proof object initial formulas used   : 4
% 0.13/0.34  # Proof object generating inferences   : 2
% 0.13/0.34  # Proof object simplifying inferences  : 6
% 0.13/0.34  # Training examples: 0 positive, 0 negative
% 0.13/0.34  # Parsed axioms                        : 7
% 0.13/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.34  # Initial clauses                      : 11
% 0.13/0.34  # Removed in clause preprocessing      : 1
% 0.13/0.34  # Initial clauses in saturation        : 10
% 0.13/0.34  # Processed clauses                    : 19
% 0.13/0.34  # ...of these trivial                  : 0
% 0.13/0.34  # ...subsumed                          : 0
% 0.13/0.34  # ...remaining for further processing  : 19
% 0.13/0.34  # Other redundant clauses eliminated   : 3
% 0.13/0.34  # Clauses deleted for lack of memory   : 0
% 0.13/0.34  # Backward-subsumed                    : 0
% 0.13/0.34  # Backward-rewritten                   : 0
% 0.13/0.34  # Generated clauses                    : 4
% 0.13/0.34  # ...of the previous two non-trivial   : 3
% 0.13/0.34  # Contextual simplify-reflections      : 0
% 0.13/0.34  # Paramodulations                      : 2
% 0.13/0.34  # Factorizations                       : 0
% 0.13/0.34  # Equation resolutions                 : 3
% 0.13/0.34  # Propositional unsat checks           : 0
% 0.13/0.34  #    Propositional check models        : 0
% 0.13/0.34  #    Propositional check unsatisfiable : 0
% 0.13/0.34  #    Propositional clauses             : 0
% 0.13/0.34  #    Propositional clauses after purity: 0
% 0.13/0.34  #    Propositional unsat core size     : 0
% 0.13/0.34  #    Propositional preprocessing time  : 0.000
% 0.13/0.34  #    Propositional encoding time       : 0.000
% 0.13/0.34  #    Propositional solver time         : 0.000
% 0.13/0.34  #    Success case prop preproc time    : 0.000
% 0.13/0.34  #    Success case prop encoding time   : 0.000
% 0.13/0.34  #    Success case prop solver time     : 0.000
% 0.13/0.34  # Current number of processed clauses  : 7
% 0.13/0.34  #    Positive orientable unit clauses  : 3
% 0.13/0.34  #    Positive unorientable unit clauses: 0
% 0.13/0.34  #    Negative unit clauses             : 2
% 0.13/0.34  #    Non-unit-clauses                  : 2
% 0.13/0.34  # Current number of unprocessed clauses: 4
% 0.13/0.34  # ...number of literals in the above   : 8
% 0.13/0.34  # Current number of archived formulas  : 0
% 0.13/0.34  # Current number of archived clauses   : 11
% 0.13/0.34  # Clause-clause subsumption calls (NU) : 0
% 0.13/0.34  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.34  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.34  # Unit Clause-clause subsumption calls : 2
% 0.13/0.34  # Rewrite failures with RHS unbound    : 0
% 0.13/0.34  # BW rewrite match attempts            : 2
% 0.13/0.34  # BW rewrite match successes           : 0
% 0.13/0.34  # Condensation attempts                : 0
% 0.13/0.34  # Condensation successes               : 0
% 0.13/0.34  # Termbank termtop insertions          : 558
% 0.13/0.34  
% 0.13/0.34  # -------------------------------------------------
% 0.13/0.34  # User time                : 0.013 s
% 0.13/0.34  # System time              : 0.005 s
% 0.13/0.34  # Total time               : 0.018 s
% 0.13/0.34  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
