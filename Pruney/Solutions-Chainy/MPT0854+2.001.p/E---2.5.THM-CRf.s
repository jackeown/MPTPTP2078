%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:00 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   26 ( 117 expanded)
%              Number of clauses        :   17 (  52 expanded)
%              Number of leaves         :    4 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :   50 ( 240 expanded)
%              Number of equality atoms :   14 (  74 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t10_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(l139_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
        & ! [X4,X5] : k4_tarski(X4,X5) != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
       => ( r2_hidden(k1_mcart_1(X1),X2)
          & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t10_mcart_1])).

fof(c_0_5,plain,(
    ! [X37,X38,X39] :
      ( ~ r2_hidden(X37,k2_zfmisc_1(X38,X39))
      | k4_tarski(esk5_1(X37),esk6_1(X37)) = X37 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).

fof(c_0_6,negated_conjecture,
    ( r2_hidden(esk11_0,k2_zfmisc_1(esk12_0,esk13_0))
    & ( ~ r2_hidden(k1_mcart_1(esk11_0),esk12_0)
      | ~ r2_hidden(k2_mcart_1(esk11_0),esk13_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X76,X77] :
      ( k1_mcart_1(k4_tarski(X76,X77)) = X76
      & k2_mcart_1(k4_tarski(X76,X77)) = X77 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_8,plain,
    ( k4_tarski(esk5_1(X1),esk6_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(esk11_0,k2_zfmisc_1(esk12_0,esk13_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( k4_tarski(esk5_1(esk11_0),esk6_1(esk11_0)) = esk11_0 ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( esk5_1(esk11_0) = k1_mcart_1(esk11_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_13,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk11_0),esk6_1(esk11_0)) = esk11_0 ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_15,plain,(
    ! [X48,X49,X50,X51] :
      ( ( r2_hidden(X48,X50)
        | ~ r2_hidden(k4_tarski(X48,X49),k2_zfmisc_1(X50,X51)) )
      & ( r2_hidden(X49,X51)
        | ~ r2_hidden(k4_tarski(X48,X49),k2_zfmisc_1(X50,X51)) )
      & ( ~ r2_hidden(X48,X50)
        | ~ r2_hidden(X49,X51)
        | r2_hidden(k4_tarski(X48,X49),k2_zfmisc_1(X50,X51)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

cnf(c_0_16,negated_conjecture,
    ( esk6_1(esk11_0) = k2_mcart_1(esk11_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk11_0),k2_mcart_1(esk11_0)) = esk11_0 ),
    inference(rw,[status(thm)],[c_0_14,c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk11_0),X1)
    | ~ r2_hidden(esk11_0,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( ~ r2_hidden(k1_mcart_1(esk11_0),esk12_0)
    | ~ r2_hidden(k2_mcart_1(esk11_0),esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk11_0),esk12_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk11_0),X1)
    | ~ r2_hidden(esk11_0,k2_zfmisc_1(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_hidden(k2_mcart_1(esk11_0),esk13_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22])])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_9]),c_0_24]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:25:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_B01_00_F1_SE_CS_SP_PS_S04AN
% 0.13/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.030 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t10_mcart_1, conjecture, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.13/0.39  fof(l139_zfmisc_1, axiom, ![X1, X2, X3]:~((r2_hidden(X1,k2_zfmisc_1(X2,X3))&![X4, X5]:k4_tarski(X4,X5)!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 0.13/0.39  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.13/0.39  fof(t106_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 0.13/0.39  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3)))), inference(assume_negation,[status(cth)],[t10_mcart_1])).
% 0.13/0.39  fof(c_0_5, plain, ![X37, X38, X39]:(~r2_hidden(X37,k2_zfmisc_1(X38,X39))|k4_tarski(esk5_1(X37),esk6_1(X37))=X37), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).
% 0.13/0.39  fof(c_0_6, negated_conjecture, (r2_hidden(esk11_0,k2_zfmisc_1(esk12_0,esk13_0))&(~r2_hidden(k1_mcart_1(esk11_0),esk12_0)|~r2_hidden(k2_mcart_1(esk11_0),esk13_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.13/0.39  fof(c_0_7, plain, ![X76, X77]:(k1_mcart_1(k4_tarski(X76,X77))=X76&k2_mcart_1(k4_tarski(X76,X77))=X77), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.13/0.39  cnf(c_0_8, plain, (k4_tarski(esk5_1(X1),esk6_1(X1))=X1|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.39  cnf(c_0_9, negated_conjecture, (r2_hidden(esk11_0,k2_zfmisc_1(esk12_0,esk13_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.39  cnf(c_0_10, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  cnf(c_0_11, negated_conjecture, (k4_tarski(esk5_1(esk11_0),esk6_1(esk11_0))=esk11_0), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.13/0.39  cnf(c_0_12, negated_conjecture, (esk5_1(esk11_0)=k1_mcart_1(esk11_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.13/0.39  cnf(c_0_13, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  cnf(c_0_14, negated_conjecture, (k4_tarski(k1_mcart_1(esk11_0),esk6_1(esk11_0))=esk11_0), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.13/0.39  fof(c_0_15, plain, ![X48, X49, X50, X51]:(((r2_hidden(X48,X50)|~r2_hidden(k4_tarski(X48,X49),k2_zfmisc_1(X50,X51)))&(r2_hidden(X49,X51)|~r2_hidden(k4_tarski(X48,X49),k2_zfmisc_1(X50,X51))))&(~r2_hidden(X48,X50)|~r2_hidden(X49,X51)|r2_hidden(k4_tarski(X48,X49),k2_zfmisc_1(X50,X51)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).
% 0.13/0.39  cnf(c_0_16, negated_conjecture, (esk6_1(esk11_0)=k2_mcart_1(esk11_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.13/0.39  cnf(c_0_17, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_18, negated_conjecture, (k4_tarski(k1_mcart_1(esk11_0),k2_mcart_1(esk11_0))=esk11_0), inference(rw,[status(thm)],[c_0_14, c_0_16])).
% 0.13/0.39  cnf(c_0_19, negated_conjecture, (r2_hidden(k1_mcart_1(esk11_0),X1)|~r2_hidden(esk11_0,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.39  cnf(c_0_20, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_21, negated_conjecture, (~r2_hidden(k1_mcart_1(esk11_0),esk12_0)|~r2_hidden(k2_mcart_1(esk11_0),esk13_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.39  cnf(c_0_22, negated_conjecture, (r2_hidden(k1_mcart_1(esk11_0),esk12_0)), inference(spm,[status(thm)],[c_0_19, c_0_9])).
% 0.13/0.39  cnf(c_0_23, negated_conjecture, (r2_hidden(k2_mcart_1(esk11_0),X1)|~r2_hidden(esk11_0,k2_zfmisc_1(X2,X1))), inference(spm,[status(thm)],[c_0_20, c_0_18])).
% 0.13/0.39  cnf(c_0_24, negated_conjecture, (~r2_hidden(k2_mcart_1(esk11_0),esk13_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22])])).
% 0.13/0.39  cnf(c_0_25, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_9]), c_0_24]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 26
% 0.13/0.39  # Proof object clause steps            : 17
% 0.13/0.39  # Proof object formula steps           : 9
% 0.13/0.39  # Proof object conjectures             : 15
% 0.13/0.39  # Proof object clause conjectures      : 12
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 7
% 0.13/0.39  # Proof object initial formulas used   : 4
% 0.13/0.39  # Proof object generating inferences   : 7
% 0.13/0.39  # Proof object simplifying inferences  : 5
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 19
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 42
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 42
% 0.13/0.39  # Processed clauses                    : 234
% 0.13/0.39  # ...of these trivial                  : 0
% 0.13/0.39  # ...subsumed                          : 45
% 0.13/0.39  # ...remaining for further processing  : 189
% 0.13/0.39  # Other redundant clauses eliminated   : 12
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 2
% 0.13/0.39  # Backward-rewritten                   : 6
% 0.13/0.39  # Generated clauses                    : 348
% 0.13/0.39  # ...of the previous two non-trivial   : 315
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 337
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 12
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 130
% 0.13/0.39  #    Positive orientable unit clauses  : 23
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 20
% 0.13/0.39  #    Non-unit-clauses                  : 87
% 0.13/0.39  # Current number of unprocessed clauses: 156
% 0.13/0.39  # ...number of literals in the above   : 438
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 50
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 2659
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 1955
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 12
% 0.13/0.39  # Unit Clause-clause subsumption calls : 457
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 17
% 0.13/0.39  # BW rewrite match successes           : 4
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 7156
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.041 s
% 0.13/0.39  # System time              : 0.005 s
% 0.13/0.39  # Total time               : 0.046 s
% 0.13/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
