%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:32 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   15 (  21 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  43 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(t18_pre_topc,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k4_subset_1(u1_struct_0(X1),X2,k3_subset_1(u1_struct_0(X1),X2)) = k2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_pre_topc)).

fof(c_0_3,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(X4))
      | k4_subset_1(X4,X5,k3_subset_1(X4,X5)) = k2_subset_1(X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_subset_1])])).

fof(c_0_4,plain,(
    ! [X3] : k2_subset_1(X3) = X3 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => k4_subset_1(u1_struct_0(X1),X2,k3_subset_1(u1_struct_0(X1),X2)) = k2_struct_0(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t18_pre_topc])).

cnf(c_0_6,plain,
    ( k4_subset_1(X2,X1,k3_subset_1(X2,X1)) = k2_subset_1(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_8,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & k4_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) != k2_struct_0(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_9,plain,
    ( k4_subset_1(X2,X1,k3_subset_1(X2,X1)) = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_6,c_0_7]),
    [final]).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) != k2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = u1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( k2_struct_0(esk1_0) != u1_struct_0(esk1_0) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:44:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___200_B02_F1_AE_CS_SP_PI_S0S
% 0.19/0.37  # and selection function SelectComplexG.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.026 s
% 0.19/0.37  
% 0.19/0.37  # No proof found!
% 0.19/0.37  # SZS status CounterSatisfiable
% 0.19/0.37  # SZS output start Saturation
% 0.19/0.37  fof(t25_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 0.19/0.37  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.19/0.37  fof(t18_pre_topc, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k4_subset_1(u1_struct_0(X1),X2,k3_subset_1(u1_struct_0(X1),X2))=k2_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_pre_topc)).
% 0.19/0.37  fof(c_0_3, plain, ![X4, X5]:(~m1_subset_1(X5,k1_zfmisc_1(X4))|k4_subset_1(X4,X5,k3_subset_1(X4,X5))=k2_subset_1(X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_subset_1])])).
% 0.19/0.37  fof(c_0_4, plain, ![X3]:k2_subset_1(X3)=X3, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.19/0.37  fof(c_0_5, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k4_subset_1(u1_struct_0(X1),X2,k3_subset_1(u1_struct_0(X1),X2))=k2_struct_0(X1)))), inference(assume_negation,[status(cth)],[t18_pre_topc])).
% 0.19/0.37  cnf(c_0_6, plain, (k4_subset_1(X2,X1,k3_subset_1(X2,X1))=k2_subset_1(X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.19/0.37  cnf(c_0_7, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.37  fof(c_0_8, negated_conjecture, (l1_struct_0(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&k4_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))!=k2_struct_0(esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.19/0.37  cnf(c_0_9, plain, (k4_subset_1(X2,X1,k3_subset_1(X2,X1))=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_6, c_0_7]), ['final']).
% 0.19/0.37  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.19/0.37  cnf(c_0_11, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))!=k2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_12, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=u1_struct_0(esk1_0)), inference(spm,[status(thm)],[c_0_9, c_0_10]), ['final']).
% 0.19/0.37  cnf(c_0_13, negated_conjecture, (k2_struct_0(esk1_0)!=u1_struct_0(esk1_0)), inference(rw,[status(thm)],[c_0_11, c_0_12]), ['final']).
% 0.19/0.37  cnf(c_0_14, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.19/0.37  # SZS output end Saturation
% 0.19/0.37  # Proof object total steps             : 15
% 0.19/0.37  # Proof object clause steps            : 8
% 0.19/0.37  # Proof object formula steps           : 7
% 0.19/0.37  # Proof object conjectures             : 8
% 0.19/0.37  # Proof object clause conjectures      : 5
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 5
% 0.19/0.37  # Proof object initial formulas used   : 3
% 0.19/0.37  # Proof object generating inferences   : 1
% 0.19/0.37  # Proof object simplifying inferences  : 2
% 0.19/0.37  # Parsed axioms                        : 3
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 5
% 0.19/0.37  # Removed in clause preprocessing      : 1
% 0.19/0.37  # Initial clauses in saturation        : 4
% 0.19/0.37  # Processed clauses                    : 6
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 0
% 0.19/0.37  # ...remaining for further processing  : 6
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 1
% 0.19/0.37  # Generated clauses                    : 1
% 0.19/0.37  # ...of the previous two non-trivial   : 2
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 1
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
% 0.19/0.37  # Current number of processed clauses  : 5
% 0.19/0.37  #    Positive orientable unit clauses  : 3
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 1
% 0.19/0.37  #    Non-unit-clauses                  : 1
% 0.19/0.37  # Current number of unprocessed clauses: 0
% 0.19/0.37  # ...number of literals in the above   : 0
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 2
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 0
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.37  # Unit Clause-clause subsumption calls : 0
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 1
% 0.19/0.37  # BW rewrite match successes           : 1
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 256
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.027 s
% 0.19/0.37  # System time              : 0.002 s
% 0.19/0.37  # Total time               : 0.030 s
% 0.19/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
