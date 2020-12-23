%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:20 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   24 (  32 expanded)
%              Number of clauses        :   13 (  14 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   58 (  83 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_xboole_0(X3,X2) )
     => r1_xboole_0(k3_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_zfmisc_1)).

fof(t94_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X3,X2) )
     => r1_tarski(k3_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(t86_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ! [X3] :
            ( r2_hidden(X3,X1)
           => r1_xboole_0(X3,X2) )
       => r1_xboole_0(k3_tarski(X1),X2) ) ),
    inference(assume_negation,[status(cth)],[t98_zfmisc_1])).

fof(c_0_6,plain,(
    ! [X17,X18] :
      ( ( r2_hidden(esk1_2(X17,X18),X17)
        | r1_tarski(k3_tarski(X17),X18) )
      & ( ~ r1_tarski(esk1_2(X17,X18),X18)
        | r1_tarski(k3_tarski(X17),X18) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).

fof(c_0_7,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | ~ r1_xboole_0(X12,X14)
      | r1_tarski(X12,k4_xboole_0(X13,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).

fof(c_0_8,negated_conjecture,(
    ! [X22] :
      ( ( ~ r2_hidden(X22,esk2_0)
        | r1_xboole_0(X22,esk3_0) )
      & ~ r1_xboole_0(k3_tarski(esk2_0),esk3_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

cnf(c_0_9,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( r1_xboole_0(X1,esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(k3_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_13,plain,(
    ! [X15,X16] :
      ( ~ r2_hidden(X15,X16)
      | r1_tarski(X15,k3_tarski(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_14,plain,
    ( r1_tarski(k3_tarski(X1),k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(esk1_2(X1,k4_xboole_0(X2,X3)),X3)
    | ~ r1_tarski(esk1_2(X1,k4_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( r1_xboole_0(esk1_2(esk2_0,X1),esk3_0)
    | r1_tarski(k3_tarski(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X4,X5,X6] :
      ( ( r1_tarski(X4,X5)
        | ~ r1_tarski(X4,k4_xboole_0(X5,X6)) )
      & ( r1_xboole_0(X4,X6)
        | ~ r1_tarski(X4,k4_xboole_0(X5,X6)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(k3_tarski(esk2_0),k4_xboole_0(X1,esk3_0))
    | ~ r1_tarski(esk1_2(esk2_0,k4_xboole_0(X1,esk3_0)),X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( r1_tarski(esk1_2(X1,X2),k3_tarski(X1))
    | r1_tarski(k3_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_12])).

cnf(c_0_20,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(k3_tarski(esk2_0),k4_xboole_0(k3_tarski(esk2_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( ~ r1_xboole_0(k3_tarski(esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n017.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 19:47:01 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.35  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.12/0.35  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.35  #
% 0.12/0.35  # Preprocessing time       : 0.027 s
% 0.12/0.35  
% 0.12/0.35  # Proof found!
% 0.12/0.35  # SZS status Theorem
% 0.12/0.35  # SZS output start CNFRefutation
% 0.12/0.35  fof(t98_zfmisc_1, conjecture, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_xboole_0(X3,X2))=>r1_xboole_0(k3_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_zfmisc_1)).
% 0.12/0.35  fof(t94_zfmisc_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X3,X2))=>r1_tarski(k3_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 0.12/0.35  fof(t86_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 0.12/0.35  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.12/0.35  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.12/0.35  fof(c_0_5, negated_conjecture, ~(![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_xboole_0(X3,X2))=>r1_xboole_0(k3_tarski(X1),X2))), inference(assume_negation,[status(cth)],[t98_zfmisc_1])).
% 0.12/0.35  fof(c_0_6, plain, ![X17, X18]:((r2_hidden(esk1_2(X17,X18),X17)|r1_tarski(k3_tarski(X17),X18))&(~r1_tarski(esk1_2(X17,X18),X18)|r1_tarski(k3_tarski(X17),X18))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).
% 0.12/0.35  fof(c_0_7, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|~r1_xboole_0(X12,X14)|r1_tarski(X12,k4_xboole_0(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).
% 0.12/0.35  fof(c_0_8, negated_conjecture, ![X22]:((~r2_hidden(X22,esk2_0)|r1_xboole_0(X22,esk3_0))&~r1_xboole_0(k3_tarski(esk2_0),esk3_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).
% 0.12/0.35  cnf(c_0_9, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.35  cnf(c_0_10, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.35  cnf(c_0_11, negated_conjecture, (r1_xboole_0(X1,esk3_0)|~r2_hidden(X1,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.35  cnf(c_0_12, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(k3_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.35  fof(c_0_13, plain, ![X15, X16]:(~r2_hidden(X15,X16)|r1_tarski(X15,k3_tarski(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.12/0.35  cnf(c_0_14, plain, (r1_tarski(k3_tarski(X1),k4_xboole_0(X2,X3))|~r1_xboole_0(esk1_2(X1,k4_xboole_0(X2,X3)),X3)|~r1_tarski(esk1_2(X1,k4_xboole_0(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.12/0.35  cnf(c_0_15, negated_conjecture, (r1_xboole_0(esk1_2(esk2_0,X1),esk3_0)|r1_tarski(k3_tarski(esk2_0),X1)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.12/0.35  cnf(c_0_16, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.35  fof(c_0_17, plain, ![X4, X5, X6]:((r1_tarski(X4,X5)|~r1_tarski(X4,k4_xboole_0(X5,X6)))&(r1_xboole_0(X4,X6)|~r1_tarski(X4,k4_xboole_0(X5,X6)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 0.12/0.35  cnf(c_0_18, negated_conjecture, (r1_tarski(k3_tarski(esk2_0),k4_xboole_0(X1,esk3_0))|~r1_tarski(esk1_2(esk2_0,k4_xboole_0(X1,esk3_0)),X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.12/0.35  cnf(c_0_19, plain, (r1_tarski(esk1_2(X1,X2),k3_tarski(X1))|r1_tarski(k3_tarski(X1),X2)), inference(spm,[status(thm)],[c_0_16, c_0_12])).
% 0.12/0.35  cnf(c_0_20, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.35  cnf(c_0_21, negated_conjecture, (r1_tarski(k3_tarski(esk2_0),k4_xboole_0(k3_tarski(esk2_0),esk3_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.35  cnf(c_0_22, negated_conjecture, (~r1_xboole_0(k3_tarski(esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.35  cnf(c_0_23, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), ['proof']).
% 0.12/0.35  # SZS output end CNFRefutation
% 0.12/0.35  # Proof object total steps             : 24
% 0.12/0.35  # Proof object clause steps            : 13
% 0.12/0.35  # Proof object formula steps           : 11
% 0.12/0.35  # Proof object conjectures             : 9
% 0.12/0.35  # Proof object clause conjectures      : 6
% 0.12/0.35  # Proof object formula conjectures     : 3
% 0.12/0.35  # Proof object initial clauses used    : 7
% 0.12/0.35  # Proof object initial formulas used   : 5
% 0.12/0.35  # Proof object generating inferences   : 6
% 0.12/0.35  # Proof object simplifying inferences  : 1
% 0.12/0.35  # Training examples: 0 positive, 0 negative
% 0.12/0.35  # Parsed axioms                        : 7
% 0.12/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.35  # Initial clauses                      : 10
% 0.12/0.35  # Removed in clause preprocessing      : 0
% 0.12/0.35  # Initial clauses in saturation        : 10
% 0.12/0.35  # Processed clauses                    : 18
% 0.12/0.35  # ...of these trivial                  : 0
% 0.12/0.35  # ...subsumed                          : 0
% 0.12/0.35  # ...remaining for further processing  : 18
% 0.12/0.35  # Other redundant clauses eliminated   : 0
% 0.12/0.35  # Clauses deleted for lack of memory   : 0
% 0.12/0.35  # Backward-subsumed                    : 0
% 0.12/0.35  # Backward-rewritten                   : 0
% 0.12/0.35  # Generated clauses                    : 17
% 0.12/0.35  # ...of the previous two non-trivial   : 11
% 0.12/0.35  # Contextual simplify-reflections      : 0
% 0.12/0.35  # Paramodulations                      : 17
% 0.12/0.35  # Factorizations                       : 0
% 0.12/0.35  # Equation resolutions                 : 0
% 0.12/0.35  # Propositional unsat checks           : 0
% 0.12/0.35  #    Propositional check models        : 0
% 0.12/0.35  #    Propositional check unsatisfiable : 0
% 0.12/0.35  #    Propositional clauses             : 0
% 0.12/0.35  #    Propositional clauses after purity: 0
% 0.12/0.35  #    Propositional unsat core size     : 0
% 0.12/0.35  #    Propositional preprocessing time  : 0.000
% 0.12/0.35  #    Propositional encoding time       : 0.000
% 0.12/0.35  #    Propositional solver time         : 0.000
% 0.12/0.35  #    Success case prop preproc time    : 0.000
% 0.12/0.35  #    Success case prop encoding time   : 0.000
% 0.12/0.35  #    Success case prop solver time     : 0.000
% 0.12/0.35  # Current number of processed clauses  : 18
% 0.12/0.35  #    Positive orientable unit clauses  : 3
% 0.12/0.35  #    Positive unorientable unit clauses: 0
% 0.12/0.35  #    Negative unit clauses             : 1
% 0.12/0.35  #    Non-unit-clauses                  : 14
% 0.12/0.35  # Current number of unprocessed clauses: 2
% 0.12/0.35  # ...number of literals in the above   : 6
% 0.12/0.35  # Current number of archived formulas  : 0
% 0.12/0.35  # Current number of archived clauses   : 0
% 0.12/0.35  # Clause-clause subsumption calls (NU) : 20
% 0.12/0.35  # Rec. Clause-clause subsumption calls : 18
% 0.12/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.35  # Unit Clause-clause subsumption calls : 1
% 0.12/0.35  # Rewrite failures with RHS unbound    : 0
% 0.12/0.35  # BW rewrite match attempts            : 0
% 0.12/0.35  # BW rewrite match successes           : 0
% 0.12/0.35  # Condensation attempts                : 0
% 0.12/0.35  # Condensation successes               : 0
% 0.12/0.35  # Termbank termtop insertions          : 955
% 0.12/0.35  
% 0.12/0.35  # -------------------------------------------------
% 0.12/0.35  # User time                : 0.025 s
% 0.12/0.35  # System time              : 0.006 s
% 0.12/0.35  # Total time               : 0.031 s
% 0.12/0.35  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
