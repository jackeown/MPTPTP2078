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
% DateTime   : Thu Dec  3 11:00:48 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   34 (  43 expanded)
%              Number of clauses        :   17 (  20 expanded)
%              Number of leaves         :    8 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  50 expanded)
%              Number of equality atoms :   16 (  25 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d6_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_wellord1)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(t8_wellord2,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_wellord1(k1_wellord2(X2),X1) = k1_wellord2(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

fof(t100_zfmisc_1,axiom,(
    ! [X1] : r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(t33_wellord2,conjecture,(
    ! [X1] : r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).

fof(c_0_8,plain,(
    ! [X5,X6] : r1_tarski(k3_xboole_0(X5,X6),X5) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_9,plain,(
    ! [X8,X9] : k1_setfam_1(k2_tarski(X8,X9)) = k3_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_10,plain,(
    ! [X3,X4] : k3_xboole_0(X3,X4) = k3_xboole_0(X4,X3) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_11,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | k2_wellord1(X10,X11) = k3_xboole_0(X10,k2_zfmisc_1(X11,X11)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_wellord1])])])).

cnf(c_0_12,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X12] : v1_relat_1(k1_wellord2(X12)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

cnf(c_0_17,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_13]),c_0_13])).

cnf(c_0_19,plain,
    ( k2_wellord1(X1,X2) = k1_setfam_1(k2_tarski(X1,k2_zfmisc_1(X2,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_15,c_0_13])).

cnf(c_0_20,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X13,X14] :
      ( ~ r1_tarski(X13,X14)
      | k2_wellord1(k1_wellord2(X14),X13) = k1_wellord2(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord2])])).

fof(c_0_22,plain,(
    ! [X7] : r1_tarski(X7,k1_zfmisc_1(k3_tarski(X7))) ),
    inference(variable_rename,[status(thm)],[t100_zfmisc_1])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1] : r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1)) ),
    inference(assume_negation,[status(cth)],[t33_wellord2])).

cnf(c_0_24,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( k1_setfam_1(k2_tarski(k1_wellord2(X1),k2_zfmisc_1(X2,X2))) = k2_wellord1(k1_wellord2(X1),X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( k2_wellord1(k1_wellord2(X2),X1) = k1_wellord2(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_28,negated_conjecture,(
    ~ r1_tarski(k1_wellord2(esk1_0),k2_zfmisc_1(esk1_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_29,plain,
    ( r1_tarski(k2_wellord1(k1_wellord2(X1),X2),k2_zfmisc_1(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( k2_wellord1(k1_wellord2(k1_zfmisc_1(k3_tarski(X1))),X1) = k1_wellord2(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_tarski(k1_wellord2(esk1_0),k2_zfmisc_1(esk1_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:48:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.36  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.18/0.36  # and selection function SelectDiffNegLit.
% 0.18/0.36  #
% 0.18/0.36  # Preprocessing time       : 0.027 s
% 0.18/0.36  # Presaturation interreduction done
% 0.18/0.36  
% 0.18/0.36  # Proof found!
% 0.18/0.36  # SZS status Theorem
% 0.18/0.36  # SZS output start CNFRefutation
% 0.18/0.36  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.18/0.36  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.18/0.36  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.18/0.36  fof(d6_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k2_wellord1(X1,X2)=k3_xboole_0(X1,k2_zfmisc_1(X2,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_wellord1)).
% 0.18/0.36  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.18/0.36  fof(t8_wellord2, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_wellord1(k1_wellord2(X2),X1)=k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_wellord2)).
% 0.18/0.36  fof(t100_zfmisc_1, axiom, ![X1]:r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 0.18/0.36  fof(t33_wellord2, conjecture, ![X1]:r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_wellord2)).
% 0.18/0.36  fof(c_0_8, plain, ![X5, X6]:r1_tarski(k3_xboole_0(X5,X6),X5), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.18/0.36  fof(c_0_9, plain, ![X8, X9]:k1_setfam_1(k2_tarski(X8,X9))=k3_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.18/0.36  fof(c_0_10, plain, ![X3, X4]:k3_xboole_0(X3,X4)=k3_xboole_0(X4,X3), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.18/0.36  fof(c_0_11, plain, ![X10, X11]:(~v1_relat_1(X10)|k2_wellord1(X10,X11)=k3_xboole_0(X10,k2_zfmisc_1(X11,X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_wellord1])])])).
% 0.18/0.36  cnf(c_0_12, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.36  cnf(c_0_13, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.36  cnf(c_0_14, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.36  cnf(c_0_15, plain, (k2_wellord1(X1,X2)=k3_xboole_0(X1,k2_zfmisc_1(X2,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.36  fof(c_0_16, plain, ![X12]:v1_relat_1(k1_wellord2(X12)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.18/0.36  cnf(c_0_17, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.18/0.36  cnf(c_0_18, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_setfam_1(k2_tarski(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_13]), c_0_13])).
% 0.18/0.36  cnf(c_0_19, plain, (k2_wellord1(X1,X2)=k1_setfam_1(k2_tarski(X1,k2_zfmisc_1(X2,X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_15, c_0_13])).
% 0.18/0.36  cnf(c_0_20, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.36  fof(c_0_21, plain, ![X13, X14]:(~r1_tarski(X13,X14)|k2_wellord1(k1_wellord2(X14),X13)=k1_wellord2(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord2])])).
% 0.18/0.36  fof(c_0_22, plain, ![X7]:r1_tarski(X7,k1_zfmisc_1(k3_tarski(X7))), inference(variable_rename,[status(thm)],[t100_zfmisc_1])).
% 0.18/0.36  fof(c_0_23, negated_conjecture, ~(![X1]:r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1))), inference(assume_negation,[status(cth)],[t33_wellord2])).
% 0.18/0.36  cnf(c_0_24, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.18/0.36  cnf(c_0_25, plain, (k1_setfam_1(k2_tarski(k1_wellord2(X1),k2_zfmisc_1(X2,X2)))=k2_wellord1(k1_wellord2(X1),X2)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.18/0.36  cnf(c_0_26, plain, (k2_wellord1(k1_wellord2(X2),X1)=k1_wellord2(X1)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.36  cnf(c_0_27, plain, (r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.36  fof(c_0_28, negated_conjecture, ~r1_tarski(k1_wellord2(esk1_0),k2_zfmisc_1(esk1_0,esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.18/0.36  cnf(c_0_29, plain, (r1_tarski(k2_wellord1(k1_wellord2(X1),X2),k2_zfmisc_1(X2,X2))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.18/0.36  cnf(c_0_30, plain, (k2_wellord1(k1_wellord2(k1_zfmisc_1(k3_tarski(X1))),X1)=k1_wellord2(X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.18/0.36  cnf(c_0_31, negated_conjecture, (~r1_tarski(k1_wellord2(esk1_0),k2_zfmisc_1(esk1_0,esk1_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.36  cnf(c_0_32, plain, (r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.18/0.36  cnf(c_0_33, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32])]), ['proof']).
% 0.18/0.36  # SZS output end CNFRefutation
% 0.18/0.36  # Proof object total steps             : 34
% 0.18/0.36  # Proof object clause steps            : 17
% 0.18/0.36  # Proof object formula steps           : 17
% 0.18/0.36  # Proof object conjectures             : 5
% 0.18/0.36  # Proof object clause conjectures      : 2
% 0.18/0.36  # Proof object formula conjectures     : 3
% 0.18/0.36  # Proof object initial clauses used    : 8
% 0.18/0.36  # Proof object initial formulas used   : 8
% 0.18/0.36  # Proof object generating inferences   : 5
% 0.18/0.36  # Proof object simplifying inferences  : 6
% 0.18/0.36  # Training examples: 0 positive, 0 negative
% 0.18/0.36  # Parsed axioms                        : 8
% 0.18/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.36  # Initial clauses                      : 8
% 0.18/0.36  # Removed in clause preprocessing      : 1
% 0.18/0.36  # Initial clauses in saturation        : 7
% 0.18/0.36  # Processed clauses                    : 23
% 0.18/0.36  # ...of these trivial                  : 1
% 0.18/0.36  # ...subsumed                          : 0
% 0.18/0.36  # ...remaining for further processing  : 22
% 0.18/0.36  # Other redundant clauses eliminated   : 0
% 0.18/0.36  # Clauses deleted for lack of memory   : 0
% 0.18/0.36  # Backward-subsumed                    : 0
% 0.18/0.36  # Backward-rewritten                   : 1
% 0.18/0.36  # Generated clauses                    : 23
% 0.18/0.36  # ...of the previous two non-trivial   : 20
% 0.18/0.36  # Contextual simplify-reflections      : 0
% 0.18/0.36  # Paramodulations                      : 23
% 0.18/0.36  # Factorizations                       : 0
% 0.18/0.36  # Equation resolutions                 : 0
% 0.18/0.36  # Propositional unsat checks           : 0
% 0.18/0.36  #    Propositional check models        : 0
% 0.18/0.36  #    Propositional check unsatisfiable : 0
% 0.18/0.36  #    Propositional clauses             : 0
% 0.18/0.36  #    Propositional clauses after purity: 0
% 0.18/0.36  #    Propositional unsat core size     : 0
% 0.18/0.36  #    Propositional preprocessing time  : 0.000
% 0.18/0.36  #    Propositional encoding time       : 0.000
% 0.18/0.36  #    Propositional solver time         : 0.000
% 0.18/0.36  #    Success case prop preproc time    : 0.000
% 0.18/0.36  #    Success case prop encoding time   : 0.000
% 0.18/0.36  #    Success case prop solver time     : 0.000
% 0.18/0.36  # Current number of processed clauses  : 14
% 0.18/0.36  #    Positive orientable unit clauses  : 11
% 0.18/0.36  #    Positive unorientable unit clauses: 1
% 0.18/0.36  #    Negative unit clauses             : 0
% 0.18/0.36  #    Non-unit-clauses                  : 2
% 0.18/0.36  # Current number of unprocessed clauses: 11
% 0.18/0.36  # ...number of literals in the above   : 11
% 0.18/0.36  # Current number of archived formulas  : 0
% 0.18/0.36  # Current number of archived clauses   : 9
% 0.18/0.36  # Clause-clause subsumption calls (NU) : 0
% 0.18/0.36  # Rec. Clause-clause subsumption calls : 0
% 0.18/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.18/0.36  # Unit Clause-clause subsumption calls : 0
% 0.18/0.36  # Rewrite failures with RHS unbound    : 0
% 0.18/0.36  # BW rewrite match attempts            : 6
% 0.18/0.36  # BW rewrite match successes           : 5
% 0.18/0.36  # Condensation attempts                : 0
% 0.18/0.36  # Condensation successes               : 0
% 0.18/0.36  # Termbank termtop insertions          : 685
% 0.18/0.36  
% 0.18/0.36  # -------------------------------------------------
% 0.18/0.36  # User time                : 0.026 s
% 0.18/0.36  # System time              : 0.005 s
% 0.18/0.36  # Total time               : 0.031 s
% 0.18/0.36  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
