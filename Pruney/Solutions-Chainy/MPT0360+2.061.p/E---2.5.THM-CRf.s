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
% DateTime   : Thu Dec  3 10:46:17 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   30 (  42 expanded)
%              Number of clauses        :   17 (  18 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   58 (  97 expanded)
%              Number of equality atoms :   15 (  27 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t40_subset_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => ( ( r1_tarski(X2,X3)
          & r1_tarski(X2,k3_subset_1(X1,X3)) )
       => X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t68_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ~ ( r1_tarski(X3,X1)
          & r1_tarski(X3,X2)
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(X1))
       => ( ( r1_tarski(X2,X3)
            & r1_tarski(X2,k3_subset_1(X1,X3)) )
         => X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t40_subset_1])).

fof(c_0_7,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(X12))
      | k3_subset_1(X12,X13) = k4_xboole_0(X12,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_8,plain,(
    ! [X5,X6] : k4_xboole_0(X5,X6) = k5_xboole_0(X5,k3_xboole_0(X5,X6)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_9,plain,(
    ! [X7,X8,X9] :
      ( v1_xboole_0(X9)
      | ~ r1_tarski(X9,X7)
      | ~ r1_tarski(X9,X8)
      | ~ r1_xboole_0(X7,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t68_xboole_1])])])).

fof(c_0_10,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
    & r1_tarski(esk2_0,esk3_0)
    & r1_tarski(esk2_0,k3_subset_1(esk1_0,esk3_0))
    & esk2_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_11,plain,(
    ! [X10,X11] : r1_xboole_0(k4_xboole_0(X10,X11),X11) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_12,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( v1_xboole_0(esk2_0)
    | ~ r1_xboole_0(X1,esk3_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(esk2_0,k3_subset_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)) = k3_subset_1(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_23,plain,(
    ! [X4] :
      ( ~ v1_xboole_0(X4)
      | X4 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_24,negated_conjecture,
    ( v1_xboole_0(esk2_0)
    | ~ r1_xboole_0(k3_subset_1(esk1_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk1_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( v1_xboole_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25])])).

cnf(c_0_28,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n012.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 13:25:07 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.32  # No SInE strategy applied
% 0.11/0.32  # Trying AutoSched0 for 299 seconds
% 0.18/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S4c
% 0.18/0.35  # and selection function SelectCQPrecWNTNp.
% 0.18/0.35  #
% 0.18/0.35  # Preprocessing time       : 0.026 s
% 0.18/0.35  # Presaturation interreduction done
% 0.18/0.35  
% 0.18/0.35  # Proof found!
% 0.18/0.35  # SZS status Theorem
% 0.18/0.35  # SZS output start CNFRefutation
% 0.18/0.35  fof(t40_subset_1, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>((r1_tarski(X2,X3)&r1_tarski(X2,k3_subset_1(X1,X3)))=>X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 0.18/0.35  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.18/0.35  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.18/0.35  fof(t68_xboole_1, axiom, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>~(((r1_tarski(X3,X1)&r1_tarski(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_xboole_1)).
% 0.18/0.35  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.18/0.35  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.18/0.35  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>((r1_tarski(X2,X3)&r1_tarski(X2,k3_subset_1(X1,X3)))=>X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t40_subset_1])).
% 0.18/0.35  fof(c_0_7, plain, ![X12, X13]:(~m1_subset_1(X13,k1_zfmisc_1(X12))|k3_subset_1(X12,X13)=k4_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.18/0.35  fof(c_0_8, plain, ![X5, X6]:k4_xboole_0(X5,X6)=k5_xboole_0(X5,k3_xboole_0(X5,X6)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.18/0.35  fof(c_0_9, plain, ![X7, X8, X9]:(v1_xboole_0(X9)|(~r1_tarski(X9,X7)|~r1_tarski(X9,X8)|~r1_xboole_0(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t68_xboole_1])])])).
% 0.18/0.35  fof(c_0_10, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))&((r1_tarski(esk2_0,esk3_0)&r1_tarski(esk2_0,k3_subset_1(esk1_0,esk3_0)))&esk2_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.18/0.35  fof(c_0_11, plain, ![X10, X11]:r1_xboole_0(k4_xboole_0(X10,X11),X11), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.18/0.35  cnf(c_0_12, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.35  cnf(c_0_13, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.35  cnf(c_0_14, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.35  cnf(c_0_15, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.35  cnf(c_0_16, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.35  cnf(c_0_17, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.18/0.35  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.35  cnf(c_0_19, negated_conjecture, (v1_xboole_0(esk2_0)|~r1_xboole_0(X1,esk3_0)|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.18/0.35  cnf(c_0_20, negated_conjecture, (r1_tarski(esk2_0,k3_subset_1(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.35  cnf(c_0_21, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_16, c_0_13])).
% 0.18/0.35  cnf(c_0_22, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0))=k3_subset_1(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.18/0.35  fof(c_0_23, plain, ![X4]:(~v1_xboole_0(X4)|X4=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.18/0.35  cnf(c_0_24, negated_conjecture, (v1_xboole_0(esk2_0)|~r1_xboole_0(k3_subset_1(esk1_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.18/0.35  cnf(c_0_25, negated_conjecture, (r1_xboole_0(k3_subset_1(esk1_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.18/0.35  cnf(c_0_26, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.35  cnf(c_0_27, negated_conjecture, (v1_xboole_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25])])).
% 0.18/0.35  cnf(c_0_28, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.35  cnf(c_0_29, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), ['proof']).
% 0.18/0.35  # SZS output end CNFRefutation
% 0.18/0.35  # Proof object total steps             : 30
% 0.18/0.35  # Proof object clause steps            : 17
% 0.18/0.35  # Proof object formula steps           : 13
% 0.18/0.35  # Proof object conjectures             : 13
% 0.18/0.35  # Proof object clause conjectures      : 10
% 0.18/0.35  # Proof object formula conjectures     : 3
% 0.18/0.35  # Proof object initial clauses used    : 9
% 0.18/0.35  # Proof object initial formulas used   : 6
% 0.18/0.35  # Proof object generating inferences   : 5
% 0.18/0.35  # Proof object simplifying inferences  : 5
% 0.18/0.35  # Training examples: 0 positive, 0 negative
% 0.18/0.35  # Parsed axioms                        : 6
% 0.18/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.35  # Initial clauses                      : 9
% 0.18/0.35  # Removed in clause preprocessing      : 1
% 0.18/0.35  # Initial clauses in saturation        : 8
% 0.18/0.35  # Processed clauses                    : 25
% 0.18/0.35  # ...of these trivial                  : 0
% 0.18/0.35  # ...subsumed                          : 0
% 0.18/0.35  # ...remaining for further processing  : 25
% 0.18/0.35  # Other redundant clauses eliminated   : 0
% 0.18/0.35  # Clauses deleted for lack of memory   : 0
% 0.18/0.35  # Backward-subsumed                    : 0
% 0.18/0.35  # Backward-rewritten                   : 6
% 0.18/0.35  # Generated clauses                    : 9
% 0.18/0.35  # ...of the previous two non-trivial   : 9
% 0.18/0.35  # Contextual simplify-reflections      : 0
% 0.18/0.35  # Paramodulations                      : 9
% 0.18/0.35  # Factorizations                       : 0
% 0.18/0.35  # Equation resolutions                 : 0
% 0.18/0.35  # Propositional unsat checks           : 0
% 0.18/0.35  #    Propositional check models        : 0
% 0.18/0.35  #    Propositional check unsatisfiable : 0
% 0.18/0.35  #    Propositional clauses             : 0
% 0.18/0.35  #    Propositional clauses after purity: 0
% 0.18/0.35  #    Propositional unsat core size     : 0
% 0.18/0.35  #    Propositional preprocessing time  : 0.000
% 0.18/0.35  #    Propositional encoding time       : 0.000
% 0.18/0.35  #    Propositional solver time         : 0.000
% 0.18/0.35  #    Success case prop preproc time    : 0.000
% 0.18/0.35  #    Success case prop encoding time   : 0.000
% 0.18/0.35  #    Success case prop solver time     : 0.000
% 0.18/0.35  # Current number of processed clauses  : 11
% 0.18/0.35  #    Positive orientable unit clauses  : 7
% 0.18/0.35  #    Positive unorientable unit clauses: 0
% 0.18/0.35  #    Negative unit clauses             : 1
% 0.18/0.35  #    Non-unit-clauses                  : 3
% 0.18/0.35  # Current number of unprocessed clauses: 0
% 0.18/0.35  # ...number of literals in the above   : 0
% 0.18/0.35  # Current number of archived formulas  : 0
% 0.18/0.35  # Current number of archived clauses   : 15
% 0.18/0.35  # Clause-clause subsumption calls (NU) : 26
% 0.18/0.35  # Rec. Clause-clause subsumption calls : 19
% 0.18/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.18/0.35  # Unit Clause-clause subsumption calls : 0
% 0.18/0.35  # Rewrite failures with RHS unbound    : 0
% 0.18/0.35  # BW rewrite match attempts            : 2
% 0.18/0.35  # BW rewrite match successes           : 2
% 0.18/0.35  # Condensation attempts                : 0
% 0.18/0.35  # Condensation successes               : 0
% 0.18/0.35  # Termbank termtop insertions          : 640
% 0.18/0.35  
% 0.18/0.35  # -------------------------------------------------
% 0.18/0.35  # User time                : 0.026 s
% 0.18/0.35  # System time              : 0.004 s
% 0.18/0.35  # Total time               : 0.030 s
% 0.18/0.35  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
