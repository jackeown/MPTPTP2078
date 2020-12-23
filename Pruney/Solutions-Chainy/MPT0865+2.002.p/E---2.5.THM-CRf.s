%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:30 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   18 (  67 expanded)
%              Number of clauses        :   11 (  26 expanded)
%              Number of leaves         :    3 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :   36 ( 167 expanded)
%              Number of equality atoms :   18 (  68 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_mcart_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,X2)
       => X1 = k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,X2)
         => X1 = k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t23_mcart_1])).

fof(c_0_4,plain,(
    ! [X5,X6,X9,X11,X12] :
      ( ( ~ v1_relat_1(X5)
        | ~ r2_hidden(X6,X5)
        | X6 = k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)) )
      & ( r2_hidden(esk3_1(X9),X9)
        | v1_relat_1(X9) )
      & ( esk3_1(X9) != k4_tarski(X11,X12)
        | v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

fof(c_0_5,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & r2_hidden(esk4_0,esk5_0)
    & esk4_0 != k4_tarski(k1_mcart_1(esk4_0),k2_mcart_1(esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_6,plain,(
    ! [X13,X14] :
      ( k1_mcart_1(k4_tarski(X13,X14)) = X13
      & k2_mcart_1(k4_tarski(X13,X14)) = X14 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_7,plain,
    ( X2 = k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( k4_tarski(esk1_2(esk5_0,esk4_0),esk2_2(esk5_0,esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])])).

cnf(c_0_12,negated_conjecture,
    ( esk1_2(esk5_0,esk4_0) = k1_mcart_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_13,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk4_0),esk2_2(esk5_0,esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( esk2_2(esk5_0,esk4_0) = k2_mcart_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_16,negated_conjecture,
    ( esk4_0 != k4_tarski(k1_mcart_1(esk4_0),k2_mcart_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.32  % Computer   : n008.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 20:31:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.13/0.35  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.13/0.35  # and selection function SelectDiffNegLit.
% 0.13/0.35  #
% 0.13/0.35  # Preprocessing time       : 0.025 s
% 0.13/0.35  # Presaturation interreduction done
% 0.13/0.35  
% 0.13/0.35  # Proof found!
% 0.13/0.35  # SZS status Theorem
% 0.13/0.35  # SZS output start CNFRefutation
% 0.13/0.35  fof(t23_mcart_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,X2)=>X1=k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 0.13/0.35  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 0.13/0.35  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.13/0.35  fof(c_0_3, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,X2)=>X1=k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1))))), inference(assume_negation,[status(cth)],[t23_mcart_1])).
% 0.13/0.35  fof(c_0_4, plain, ![X5, X6, X9, X11, X12]:((~v1_relat_1(X5)|(~r2_hidden(X6,X5)|X6=k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6))))&((r2_hidden(esk3_1(X9),X9)|v1_relat_1(X9))&(esk3_1(X9)!=k4_tarski(X11,X12)|v1_relat_1(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.13/0.35  fof(c_0_5, negated_conjecture, (v1_relat_1(esk5_0)&(r2_hidden(esk4_0,esk5_0)&esk4_0!=k4_tarski(k1_mcart_1(esk4_0),k2_mcart_1(esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.13/0.35  fof(c_0_6, plain, ![X13, X14]:(k1_mcart_1(k4_tarski(X13,X14))=X13&k2_mcart_1(k4_tarski(X13,X14))=X14), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.13/0.35  cnf(c_0_7, plain, (X2=k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2))|~v1_relat_1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.35  cnf(c_0_8, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.35  cnf(c_0_9, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.35  cnf(c_0_10, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.35  cnf(c_0_11, negated_conjecture, (k4_tarski(esk1_2(esk5_0,esk4_0),esk2_2(esk5_0,esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_9])])).
% 0.13/0.35  cnf(c_0_12, negated_conjecture, (esk1_2(esk5_0,esk4_0)=k1_mcart_1(esk4_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.13/0.35  cnf(c_0_13, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.35  cnf(c_0_14, negated_conjecture, (k4_tarski(k1_mcart_1(esk4_0),esk2_2(esk5_0,esk4_0))=esk4_0), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.13/0.35  cnf(c_0_15, negated_conjecture, (esk2_2(esk5_0,esk4_0)=k2_mcart_1(esk4_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.13/0.35  cnf(c_0_16, negated_conjecture, (esk4_0!=k4_tarski(k1_mcart_1(esk4_0),k2_mcart_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.35  cnf(c_0_17, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_15]), c_0_16]), ['proof']).
% 0.13/0.35  # SZS output end CNFRefutation
% 0.13/0.35  # Proof object total steps             : 18
% 0.13/0.35  # Proof object clause steps            : 11
% 0.13/0.35  # Proof object formula steps           : 7
% 0.13/0.35  # Proof object conjectures             : 11
% 0.13/0.35  # Proof object clause conjectures      : 8
% 0.13/0.35  # Proof object formula conjectures     : 3
% 0.13/0.35  # Proof object initial clauses used    : 6
% 0.13/0.35  # Proof object initial formulas used   : 3
% 0.13/0.35  # Proof object generating inferences   : 3
% 0.13/0.35  # Proof object simplifying inferences  : 5
% 0.13/0.35  # Training examples: 0 positive, 0 negative
% 0.13/0.35  # Parsed axioms                        : 3
% 0.13/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.35  # Initial clauses                      : 8
% 0.13/0.35  # Removed in clause preprocessing      : 0
% 0.13/0.35  # Initial clauses in saturation        : 8
% 0.13/0.35  # Processed clauses                    : 21
% 0.13/0.35  # ...of these trivial                  : 0
% 0.13/0.35  # ...subsumed                          : 0
% 0.13/0.35  # ...remaining for further processing  : 21
% 0.13/0.35  # Other redundant clauses eliminated   : 0
% 0.13/0.35  # Clauses deleted for lack of memory   : 0
% 0.13/0.35  # Backward-subsumed                    : 0
% 0.13/0.35  # Backward-rewritten                   : 2
% 0.13/0.35  # Generated clauses                    : 7
% 0.13/0.35  # ...of the previous two non-trivial   : 7
% 0.13/0.35  # Contextual simplify-reflections      : 0
% 0.13/0.35  # Paramodulations                      : 7
% 0.13/0.35  # Factorizations                       : 0
% 0.13/0.35  # Equation resolutions                 : 0
% 0.13/0.35  # Propositional unsat checks           : 0
% 0.13/0.35  #    Propositional check models        : 0
% 0.13/0.35  #    Propositional check unsatisfiable : 0
% 0.13/0.35  #    Propositional clauses             : 0
% 0.13/0.35  #    Propositional clauses after purity: 0
% 0.13/0.35  #    Propositional unsat core size     : 0
% 0.13/0.35  #    Propositional preprocessing time  : 0.000
% 0.13/0.35  #    Propositional encoding time       : 0.000
% 0.13/0.35  #    Propositional solver time         : 0.000
% 0.13/0.35  #    Success case prop preproc time    : 0.000
% 0.13/0.35  #    Success case prop encoding time   : 0.000
% 0.13/0.35  #    Success case prop solver time     : 0.000
% 0.13/0.35  # Current number of processed clauses  : 11
% 0.13/0.35  #    Positive orientable unit clauses  : 6
% 0.13/0.35  #    Positive unorientable unit clauses: 0
% 0.13/0.35  #    Negative unit clauses             : 1
% 0.13/0.35  #    Non-unit-clauses                  : 4
% 0.13/0.35  # Current number of unprocessed clauses: 0
% 0.13/0.35  # ...number of literals in the above   : 0
% 0.13/0.35  # Current number of archived formulas  : 0
% 0.13/0.35  # Current number of archived clauses   : 10
% 0.13/0.35  # Clause-clause subsumption calls (NU) : 0
% 0.13/0.35  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.35  # Unit Clause-clause subsumption calls : 0
% 0.13/0.35  # Rewrite failures with RHS unbound    : 0
% 0.13/0.35  # BW rewrite match attempts            : 2
% 0.13/0.35  # BW rewrite match successes           : 2
% 0.13/0.35  # Condensation attempts                : 0
% 0.13/0.35  # Condensation successes               : 0
% 0.13/0.35  # Termbank termtop insertions          : 488
% 0.13/0.35  
% 0.13/0.35  # -------------------------------------------------
% 0.13/0.35  # User time                : 0.026 s
% 0.13/0.35  # System time              : 0.003 s
% 0.13/0.35  # Total time               : 0.029 s
% 0.13/0.35  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
