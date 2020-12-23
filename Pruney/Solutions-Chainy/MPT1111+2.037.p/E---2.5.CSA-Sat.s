%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:11 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   25 (  93 expanded)
%              Number of clauses        :   16 (  36 expanded)
%              Number of leaves         :    4 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   75 ( 355 expanded)
%              Number of equality atoms :   20 (  75 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_pre_topc)).

fof(t4_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5] :
                  ( ( r2_hidden(X3,X4)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X5,X2) )
                 => r1_xboole_0(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_mcart_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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
    ! [X9,X11,X12,X13] :
      ( ( r2_hidden(esk1_1(X9),X9)
        | X9 = k1_xboole_0 )
      & ( ~ r2_hidden(X11,X12)
        | ~ r2_hidden(X12,X13)
        | ~ r2_hidden(X13,esk1_1(X9))
        | r1_xboole_0(X11,X9)
        | X9 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_mcart_1])])])])])])).

fof(c_0_6,plain,(
    ! [X6,X7,X8] :
      ( ~ r2_hidden(X6,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X8))
      | m1_subset_1(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_7,negated_conjecture,(
    ! [X17] :
      ( l1_pre_topc(esk2_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
      & esk3_0 != k1_struct_0(esk2_0)
      & ( ~ m1_subset_1(X17,u1_struct_0(esk2_0))
        | ~ r2_hidden(X17,esk3_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])).

cnf(c_0_8,plain,
    ( r1_xboole_0(X1,X4)
    | X4 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X3,esk1_1(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_9,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_10,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( esk1_1(X1) = k1_xboole_0
    | X1 = k1_xboole_0
    | r1_xboole_0(X2,X1)
    | ~ r2_hidden(X3,esk1_1(esk1_1(X1)))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])).

cnf(c_0_15,plain,
    ( esk1_1(esk1_1(X1)) = k1_xboole_0
    | esk1_1(X1) = k1_xboole_0
    | X1 = k1_xboole_0
    | r1_xboole_0(X2,X1)
    | ~ r2_hidden(X2,esk1_1(esk1_1(esk1_1(X1)))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_9]),
    [final]).

fof(c_0_16,plain,(
    ! [X14] :
      ( ~ l1_pre_topc(X14)
      | l1_struct_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_17,negated_conjecture,
    ( esk3_0 != k1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_9]),
    [final]).

cnf(c_0_19,plain,
    ( esk1_1(esk1_1(esk1_1(X1))) = k1_xboole_0
    | esk1_1(esk1_1(X1)) = k1_xboole_0
    | esk1_1(X1) = k1_xboole_0
    | X1 = k1_xboole_0
    | r1_xboole_0(esk1_1(esk1_1(esk1_1(esk1_1(X1)))),X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_9]),
    [final]).

cnf(c_0_20,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( k1_struct_0(esk2_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_17,c_0_18]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_14,c_0_18]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_11,c_0_18]),
    [final]).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_____0026_C18_F1_SE_CS_SP_S4S
% 0.19/0.37  # and selection function SelectNewComplexAHPNS.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.026 s
% 0.19/0.37  
% 0.19/0.37  # No proof found!
% 0.19/0.37  # SZS status CounterSatisfiable
% 0.19/0.37  # SZS output start Saturation
% 0.19/0.37  fof(t41_pre_topc, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>~((X2!=k1_struct_0(X1)&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~(r2_hidden(X3,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_pre_topc)).
% 0.19/0.37  fof(t4_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5]:(((r2_hidden(X3,X4)&r2_hidden(X4,X5))&r2_hidden(X5,X2))=>r1_xboole_0(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_mcart_1)).
% 0.19/0.37  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.37  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.37  fof(c_0_4, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>~((X2!=k1_struct_0(X1)&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~(r2_hidden(X3,X2)))))))), inference(assume_negation,[status(cth)],[t41_pre_topc])).
% 0.19/0.37  fof(c_0_5, plain, ![X9, X11, X12, X13]:((r2_hidden(esk1_1(X9),X9)|X9=k1_xboole_0)&(~r2_hidden(X11,X12)|~r2_hidden(X12,X13)|~r2_hidden(X13,esk1_1(X9))|r1_xboole_0(X11,X9)|X9=k1_xboole_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_mcart_1])])])])])])).
% 0.19/0.37  fof(c_0_6, plain, ![X6, X7, X8]:(~r2_hidden(X6,X7)|~m1_subset_1(X7,k1_zfmisc_1(X8))|m1_subset_1(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.37  fof(c_0_7, negated_conjecture, ![X17]:(l1_pre_topc(esk2_0)&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(esk3_0!=k1_struct_0(esk2_0)&(~m1_subset_1(X17,u1_struct_0(esk2_0))|~r2_hidden(X17,esk3_0))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])).
% 0.19/0.37  cnf(c_0_8, plain, (r1_xboole_0(X1,X4)|X4=k1_xboole_0|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|~r2_hidden(X3,esk1_1(X4))), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.19/0.37  cnf(c_0_9, plain, (r2_hidden(esk1_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.19/0.37  cnf(c_0_10, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.19/0.37  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_12, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_13, plain, (esk1_1(X1)=k1_xboole_0|X1=k1_xboole_0|r1_xboole_0(X2,X1)|~r2_hidden(X3,esk1_1(esk1_1(X1)))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_8, c_0_9]), ['final']).
% 0.19/0.37  cnf(c_0_14, negated_conjecture, (~r2_hidden(X1,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12])).
% 0.19/0.37  cnf(c_0_15, plain, (esk1_1(esk1_1(X1))=k1_xboole_0|esk1_1(X1)=k1_xboole_0|X1=k1_xboole_0|r1_xboole_0(X2,X1)|~r2_hidden(X2,esk1_1(esk1_1(esk1_1(X1))))), inference(spm,[status(thm)],[c_0_13, c_0_9]), ['final']).
% 0.19/0.37  fof(c_0_16, plain, ![X14]:(~l1_pre_topc(X14)|l1_struct_0(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.37  cnf(c_0_17, negated_conjecture, (esk3_0!=k1_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_14, c_0_9]), ['final']).
% 0.19/0.37  cnf(c_0_19, plain, (esk1_1(esk1_1(esk1_1(X1)))=k1_xboole_0|esk1_1(esk1_1(X1))=k1_xboole_0|esk1_1(X1)=k1_xboole_0|X1=k1_xboole_0|r1_xboole_0(esk1_1(esk1_1(esk1_1(esk1_1(X1)))),X1)), inference(spm,[status(thm)],[c_0_15, c_0_9]), ['final']).
% 0.19/0.37  cnf(c_0_20, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.19/0.37  cnf(c_0_21, negated_conjecture, (k1_struct_0(esk2_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_17, c_0_18]), ['final']).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_14, c_0_18]), ['final']).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(rw,[status(thm)],[c_0_11, c_0_18]), ['final']).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.19/0.37  # SZS output end Saturation
% 0.19/0.37  # Proof object total steps             : 25
% 0.19/0.37  # Proof object clause steps            : 16
% 0.19/0.37  # Proof object formula steps           : 9
% 0.19/0.37  # Proof object conjectures             : 12
% 0.19/0.37  # Proof object clause conjectures      : 9
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 8
% 0.19/0.37  # Proof object initial formulas used   : 4
% 0.19/0.37  # Proof object generating inferences   : 5
% 0.19/0.37  # Proof object simplifying inferences  : 4
% 0.19/0.37  # Parsed axioms                        : 4
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 8
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 8
% 0.19/0.37  # Processed clauses                    : 19
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 2
% 0.19/0.37  # ...remaining for further processing  : 17
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 5
% 0.19/0.37  # Generated clauses                    : 7
% 0.19/0.37  # ...of the previous two non-trivial   : 11
% 0.19/0.37  # Contextual simplify-reflections      : 1
% 0.19/0.37  # Paramodulations                      : 7
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 0
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 12
% 0.19/0.37  #    Positive orientable unit clauses  : 3
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 2
% 0.19/0.37  #    Non-unit-clauses                  : 7
% 0.19/0.37  # Current number of unprocessed clauses: 0
% 0.19/0.37  # ...number of literals in the above   : 0
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 5
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 5
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 1
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.19/0.37  # Unit Clause-clause subsumption calls : 3
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 1
% 0.19/0.37  # BW rewrite match successes           : 1
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 761
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.027 s
% 0.19/0.37  # System time              : 0.003 s
% 0.19/0.37  # Total time               : 0.030 s
% 0.19/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
