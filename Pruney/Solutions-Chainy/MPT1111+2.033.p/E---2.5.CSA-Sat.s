%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:10 EST 2020

% Result     : CounterSatisfiable 0.12s
% Output     : Saturation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   22 (  81 expanded)
%              Number of clauses        :   13 (  30 expanded)
%              Number of leaves         :    4 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   51 ( 268 expanded)
%              Number of equality atoms :   11 (  54 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    5 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_pre_topc,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ~ ( X2 != k1_struct_0(X1)
              & ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ~ r2_hidden(X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_pre_topc)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t1_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ~ ( X2 != k1_struct_0(X1)
                & ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ~ r2_hidden(X3,X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t41_pre_topc])).

fof(c_0_5,plain,(
    ! [X4,X5,X6] :
      ( ~ r2_hidden(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X6))
      | m1_subset_1(X4,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_6,negated_conjecture,(
    ! [X12] :
      ( l1_pre_topc(esk2_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
      & esk3_0 != k1_struct_0(esk2_0)
      & ( ~ m1_subset_1(X12,u1_struct_0(esk2_0))
        | ~ r2_hidden(X12,esk3_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])).

cnf(c_0_7,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_8,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X7] :
      ( ( r2_hidden(esk1_1(X7),X7)
        | X7 = k1_xboole_0 )
      & ( r1_xboole_0(esk1_1(X7),X7)
        | X7 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_mcart_1])])])])).

cnf(c_0_11,negated_conjecture,
    ( ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])).

cnf(c_0_12,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

fof(c_0_13,plain,(
    ! [X9] :
      ( ~ l1_pre_topc(X9)
      | l1_struct_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_14,negated_conjecture,
    ( esk3_0 != k1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_11,c_0_12]),
    [final]).

cnf(c_0_16,plain,
    ( r1_xboole_0(esk1_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_17,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_18,negated_conjecture,
    ( k1_struct_0(esk2_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_14,c_0_15]),
    [final]).

cnf(c_0_19,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_11,c_0_15]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_8,c_0_15]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:40:50 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.35  # AutoSched0-Mode selected heuristic G_____0026_C18_F1_SE_CS_SP_S4S
% 0.12/0.35  # and selection function SelectNewComplexAHPNS.
% 0.12/0.35  #
% 0.12/0.35  # Preprocessing time       : 0.015 s
% 0.12/0.35  
% 0.12/0.35  # No proof found!
% 0.12/0.35  # SZS status CounterSatisfiable
% 0.12/0.35  # SZS output start Saturation
% 0.12/0.35  fof(t41_pre_topc, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>~((X2!=k1_struct_0(X1)&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~(r2_hidden(X3,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_pre_topc)).
% 0.12/0.35  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.12/0.35  fof(t1_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&r1_xboole_0(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 0.12/0.35  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.12/0.35  fof(c_0_4, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>~((X2!=k1_struct_0(X1)&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~(r2_hidden(X3,X2)))))))), inference(assume_negation,[status(cth)],[t41_pre_topc])).
% 0.12/0.35  fof(c_0_5, plain, ![X4, X5, X6]:(~r2_hidden(X4,X5)|~m1_subset_1(X5,k1_zfmisc_1(X6))|m1_subset_1(X4,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.12/0.35  fof(c_0_6, negated_conjecture, ![X12]:(l1_pre_topc(esk2_0)&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(esk3_0!=k1_struct_0(esk2_0)&(~m1_subset_1(X12,u1_struct_0(esk2_0))|~r2_hidden(X12,esk3_0))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])).
% 0.12/0.35  cnf(c_0_7, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.12/0.35  cnf(c_0_8, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.35  cnf(c_0_9, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.35  fof(c_0_10, plain, ![X7]:((r2_hidden(esk1_1(X7),X7)|X7=k1_xboole_0)&(r1_xboole_0(esk1_1(X7),X7)|X7=k1_xboole_0)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_mcart_1])])])])).
% 0.12/0.35  cnf(c_0_11, negated_conjecture, (~r2_hidden(X1,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_9])).
% 0.12/0.35  cnf(c_0_12, plain, (r2_hidden(esk1_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.12/0.35  fof(c_0_13, plain, ![X9]:(~l1_pre_topc(X9)|l1_struct_0(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.12/0.35  cnf(c_0_14, negated_conjecture, (esk3_0!=k1_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.35  cnf(c_0_15, negated_conjecture, (esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_11, c_0_12]), ['final']).
% 0.12/0.35  cnf(c_0_16, plain, (r1_xboole_0(esk1_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.12/0.35  cnf(c_0_17, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.12/0.35  cnf(c_0_18, negated_conjecture, (k1_struct_0(esk2_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_14, c_0_15]), ['final']).
% 0.12/0.35  cnf(c_0_19, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_11, c_0_15]), ['final']).
% 0.12/0.35  cnf(c_0_20, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(rw,[status(thm)],[c_0_8, c_0_15]), ['final']).
% 0.12/0.35  cnf(c_0_21, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.12/0.35  # SZS output end Saturation
% 0.12/0.35  # Proof object total steps             : 22
% 0.12/0.35  # Proof object clause steps            : 13
% 0.12/0.35  # Proof object formula steps           : 9
% 0.12/0.35  # Proof object conjectures             : 12
% 0.12/0.35  # Proof object clause conjectures      : 9
% 0.12/0.35  # Proof object formula conjectures     : 3
% 0.12/0.35  # Proof object initial clauses used    : 8
% 0.12/0.35  # Proof object initial formulas used   : 4
% 0.12/0.35  # Proof object generating inferences   : 2
% 0.12/0.35  # Proof object simplifying inferences  : 4
% 0.12/0.35  # Parsed axioms                        : 4
% 0.12/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.35  # Initial clauses                      : 8
% 0.12/0.35  # Removed in clause preprocessing      : 0
% 0.12/0.35  # Initial clauses in saturation        : 8
% 0.12/0.35  # Processed clauses                    : 16
% 0.12/0.35  # ...of these trivial                  : 0
% 0.12/0.35  # ...subsumed                          : 2
% 0.12/0.35  # ...remaining for further processing  : 14
% 0.12/0.35  # Other redundant clauses eliminated   : 0
% 0.12/0.35  # Clauses deleted for lack of memory   : 0
% 0.12/0.35  # Backward-subsumed                    : 0
% 0.12/0.35  # Backward-rewritten                   : 5
% 0.12/0.35  # Generated clauses                    : 4
% 0.12/0.35  # ...of the previous two non-trivial   : 8
% 0.12/0.35  # Contextual simplify-reflections      : 1
% 0.12/0.35  # Paramodulations                      : 4
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
% 0.12/0.35  # Current number of processed clauses  : 9
% 0.12/0.35  #    Positive orientable unit clauses  : 3
% 0.12/0.35  #    Positive unorientable unit clauses: 0
% 0.12/0.35  #    Negative unit clauses             : 2
% 0.12/0.35  #    Non-unit-clauses                  : 4
% 0.12/0.35  # Current number of unprocessed clauses: 0
% 0.12/0.35  # ...number of literals in the above   : 0
% 0.12/0.35  # Current number of archived formulas  : 0
% 0.12/0.35  # Current number of archived clauses   : 5
% 0.12/0.35  # Clause-clause subsumption calls (NU) : 1
% 0.12/0.35  # Rec. Clause-clause subsumption calls : 1
% 0.12/0.35  # Non-unit clause-clause subsumptions  : 1
% 0.12/0.35  # Unit Clause-clause subsumption calls : 4
% 0.12/0.35  # Rewrite failures with RHS unbound    : 0
% 0.12/0.35  # BW rewrite match attempts            : 1
% 0.12/0.35  # BW rewrite match successes           : 1
% 0.12/0.35  # Condensation attempts                : 0
% 0.12/0.35  # Condensation successes               : 0
% 0.12/0.35  # Termbank termtop insertions          : 533
% 0.12/0.35  
% 0.12/0.35  # -------------------------------------------------
% 0.12/0.35  # User time                : 0.015 s
% 0.12/0.35  # System time              : 0.003 s
% 0.12/0.35  # Total time               : 0.018 s
% 0.12/0.35  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
