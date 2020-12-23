%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:34 EST 2020

% Result     : Theorem 0.16s
% Output     : CNFRefutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   41 (  98 expanded)
%              Number of clauses        :   24 (  43 expanded)
%              Number of leaves         :    8 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   59 ( 142 expanded)
%              Number of equality atoms :   39 (  91 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t213_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k6_subset_1(k1_relat_1(X2),k1_relat_1(k7_relat_1(X2,X1))) = k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t109_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k7_relat_1(X3,X1),k7_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t191_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,k6_subset_1(k1_relat_1(X2),X1))) = k6_subset_1(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => k6_subset_1(k1_relat_1(X2),k1_relat_1(k7_relat_1(X2,X1))) = k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1))) ) ),
    inference(assume_negation,[status(cth)],[t213_relat_1])).

fof(c_0_9,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | k1_relat_1(k7_relat_1(X16,X15)) = k3_xboole_0(k1_relat_1(X16),X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

fof(c_0_10,plain,(
    ! [X8,X9] : k1_setfam_1(k2_tarski(X8,X9)) = k3_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_11,plain,(
    ! [X10,X11,X12] :
      ( ~ v1_relat_1(X12)
      | k7_relat_1(X12,k6_subset_1(X10,X11)) = k6_subset_1(k7_relat_1(X12,X10),k7_relat_1(X12,X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_relat_1])])).

fof(c_0_12,plain,(
    ! [X6,X7] : k6_subset_1(X6,X7) = k4_xboole_0(X6,X7) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_13,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X14)
      | k1_relat_1(k7_relat_1(X14,k6_subset_1(k1_relat_1(X14),X13))) = k6_subset_1(k1_relat_1(X14),X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t191_relat_1])])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & k6_subset_1(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk2_0,esk1_0))) != k1_relat_1(k6_subset_1(esk2_0,k7_relat_1(esk2_0,esk1_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_15,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k7_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k7_relat_1(X1,X2),k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X2))) = k6_subset_1(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( k6_subset_1(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk2_0,esk1_0))) != k1_relat_1(k6_subset_1(esk2_0,k7_relat_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_23,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k3_xboole_0(X4,X5)) = k4_xboole_0(X4,X5) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_24,plain,
    ( k7_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k7_relat_1(X1,X2),k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_18])).

fof(c_0_25,plain,(
    ! [X17] :
      ( ~ v1_relat_1(X17)
      | k7_relat_1(X17,k1_relat_1(X17)) = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

cnf(c_0_26,plain,
    ( k1_relat_1(k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),X2))) = k4_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_18]),c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( k4_xboole_0(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk2_0,esk1_0))) != k1_relat_1(k4_xboole_0(esk2_0,k7_relat_1(esk2_0,esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_18]),c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,X1)) = k1_setfam_1(k2_tarski(k1_relat_1(esk2_0),X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( k7_relat_1(esk2_0,k4_xboole_0(X1,X2)) = k4_xboole_0(k7_relat_1(esk2_0,X1),k7_relat_1(esk2_0,X2)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_22])).

cnf(c_0_31,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,k4_xboole_0(k1_relat_1(esk2_0),X1))) = k4_xboole_0(k1_relat_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( k1_relat_1(k4_xboole_0(esk2_0,k7_relat_1(esk2_0,esk1_0))) != k4_xboole_0(k1_relat_1(esk2_0),k1_setfam_1(k2_tarski(k1_relat_1(esk2_0),esk1_0))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_16])).

cnf(c_0_35,negated_conjecture,
    ( k1_relat_1(k4_xboole_0(k7_relat_1(esk2_0,X1),k7_relat_1(esk2_0,X2))) = k1_setfam_1(k2_tarski(k1_relat_1(esk2_0),k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( k7_relat_1(esk2_0,k1_relat_1(esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_22])).

cnf(c_0_37,negated_conjecture,
    ( k1_setfam_1(k2_tarski(k1_relat_1(esk2_0),k4_xboole_0(k1_relat_1(esk2_0),X1))) = k4_xboole_0(k1_relat_1(esk2_0),X1) ),
    inference(rw,[status(thm)],[c_0_32,c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( k1_relat_1(k4_xboole_0(esk2_0,k7_relat_1(esk2_0,esk1_0))) != k4_xboole_0(k1_relat_1(esk2_0),esk1_0) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( k1_relat_1(k4_xboole_0(esk2_0,k7_relat_1(esk2_0,X1))) = k4_xboole_0(k1_relat_1(esk2_0),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.30  % Computer   : n015.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % WCLimit    : 600
% 0.11/0.30  % DateTime   : Tue Dec  1 09:34:53 EST 2020
% 0.11/0.30  % CPUTime    : 
% 0.16/0.31  # Version: 2.5pre002
% 0.16/0.31  # No SInE strategy applied
% 0.16/0.31  # Trying AutoSched0 for 299 seconds
% 0.16/0.33  # AutoSched0-Mode selected heuristic G_E___208_B00_00_F1_SE_CS_SP_PS_S070I
% 0.16/0.33  # and selection function SelectVGNonCR.
% 0.16/0.33  #
% 0.16/0.33  # Preprocessing time       : 0.026 s
% 0.16/0.33  # Presaturation interreduction done
% 0.16/0.33  
% 0.16/0.33  # Proof found!
% 0.16/0.33  # SZS status Theorem
% 0.16/0.33  # SZS output start CNFRefutation
% 0.16/0.33  fof(t213_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>k6_subset_1(k1_relat_1(X2),k1_relat_1(k7_relat_1(X2,X1)))=k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t213_relat_1)).
% 0.16/0.33  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 0.16/0.33  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.16/0.33  fof(t109_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k7_relat_1(X3,X1),k7_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_relat_1)).
% 0.16/0.33  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.16/0.33  fof(t191_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,k6_subset_1(k1_relat_1(X2),X1)))=k6_subset_1(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_relat_1)).
% 0.16/0.33  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.16/0.33  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 0.16/0.33  fof(c_0_8, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>k6_subset_1(k1_relat_1(X2),k1_relat_1(k7_relat_1(X2,X1)))=k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1))))), inference(assume_negation,[status(cth)],[t213_relat_1])).
% 0.16/0.33  fof(c_0_9, plain, ![X15, X16]:(~v1_relat_1(X16)|k1_relat_1(k7_relat_1(X16,X15))=k3_xboole_0(k1_relat_1(X16),X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.16/0.33  fof(c_0_10, plain, ![X8, X9]:k1_setfam_1(k2_tarski(X8,X9))=k3_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.16/0.33  fof(c_0_11, plain, ![X10, X11, X12]:(~v1_relat_1(X12)|k7_relat_1(X12,k6_subset_1(X10,X11))=k6_subset_1(k7_relat_1(X12,X10),k7_relat_1(X12,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_relat_1])])).
% 0.16/0.33  fof(c_0_12, plain, ![X6, X7]:k6_subset_1(X6,X7)=k4_xboole_0(X6,X7), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.16/0.33  fof(c_0_13, plain, ![X13, X14]:(~v1_relat_1(X14)|k1_relat_1(k7_relat_1(X14,k6_subset_1(k1_relat_1(X14),X13)))=k6_subset_1(k1_relat_1(X14),X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t191_relat_1])])).
% 0.16/0.33  fof(c_0_14, negated_conjecture, (v1_relat_1(esk2_0)&k6_subset_1(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk2_0,esk1_0)))!=k1_relat_1(k6_subset_1(esk2_0,k7_relat_1(esk2_0,esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.16/0.33  cnf(c_0_15, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.16/0.33  cnf(c_0_16, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.16/0.33  cnf(c_0_17, plain, (k7_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k7_relat_1(X1,X2),k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.16/0.33  cnf(c_0_18, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.16/0.33  cnf(c_0_19, plain, (k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X2)))=k6_subset_1(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.16/0.33  cnf(c_0_20, negated_conjecture, (k6_subset_1(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk2_0,esk1_0)))!=k1_relat_1(k6_subset_1(esk2_0,k7_relat_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.16/0.33  cnf(c_0_21, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k2_tarski(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.16/0.33  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.16/0.33  fof(c_0_23, plain, ![X4, X5]:k4_xboole_0(X4,k3_xboole_0(X4,X5))=k4_xboole_0(X4,X5), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.16/0.33  cnf(c_0_24, plain, (k7_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k7_relat_1(X1,X2),k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_18])).
% 0.16/0.33  fof(c_0_25, plain, ![X17]:(~v1_relat_1(X17)|k7_relat_1(X17,k1_relat_1(X17))=X17), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.16/0.33  cnf(c_0_26, plain, (k1_relat_1(k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),X2)))=k4_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_18]), c_0_18])).
% 0.16/0.33  cnf(c_0_27, negated_conjecture, (k4_xboole_0(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk2_0,esk1_0)))!=k1_relat_1(k4_xboole_0(esk2_0,k7_relat_1(esk2_0,esk1_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_18]), c_0_18])).
% 0.16/0.33  cnf(c_0_28, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,X1))=k1_setfam_1(k2_tarski(k1_relat_1(esk2_0),X1))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.16/0.33  cnf(c_0_29, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.16/0.33  cnf(c_0_30, negated_conjecture, (k7_relat_1(esk2_0,k4_xboole_0(X1,X2))=k4_xboole_0(k7_relat_1(esk2_0,X1),k7_relat_1(esk2_0,X2))), inference(spm,[status(thm)],[c_0_24, c_0_22])).
% 0.16/0.33  cnf(c_0_31, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.16/0.33  cnf(c_0_32, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,k4_xboole_0(k1_relat_1(esk2_0),X1)))=k4_xboole_0(k1_relat_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_26, c_0_22])).
% 0.16/0.33  cnf(c_0_33, negated_conjecture, (k1_relat_1(k4_xboole_0(esk2_0,k7_relat_1(esk2_0,esk1_0)))!=k4_xboole_0(k1_relat_1(esk2_0),k1_setfam_1(k2_tarski(k1_relat_1(esk2_0),esk1_0)))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.16/0.33  cnf(c_0_34, plain, (k4_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_29, c_0_16])).
% 0.16/0.33  cnf(c_0_35, negated_conjecture, (k1_relat_1(k4_xboole_0(k7_relat_1(esk2_0,X1),k7_relat_1(esk2_0,X2)))=k1_setfam_1(k2_tarski(k1_relat_1(esk2_0),k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_28, c_0_30])).
% 0.16/0.33  cnf(c_0_36, negated_conjecture, (k7_relat_1(esk2_0,k1_relat_1(esk2_0))=esk2_0), inference(spm,[status(thm)],[c_0_31, c_0_22])).
% 0.16/0.33  cnf(c_0_37, negated_conjecture, (k1_setfam_1(k2_tarski(k1_relat_1(esk2_0),k4_xboole_0(k1_relat_1(esk2_0),X1)))=k4_xboole_0(k1_relat_1(esk2_0),X1)), inference(rw,[status(thm)],[c_0_32, c_0_28])).
% 0.16/0.33  cnf(c_0_38, negated_conjecture, (k1_relat_1(k4_xboole_0(esk2_0,k7_relat_1(esk2_0,esk1_0)))!=k4_xboole_0(k1_relat_1(esk2_0),esk1_0)), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.16/0.33  cnf(c_0_39, negated_conjecture, (k1_relat_1(k4_xboole_0(esk2_0,k7_relat_1(esk2_0,X1)))=k4_xboole_0(k1_relat_1(esk2_0),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.16/0.33  cnf(c_0_40, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39])]), ['proof']).
% 0.16/0.33  # SZS output end CNFRefutation
% 0.16/0.33  # Proof object total steps             : 41
% 0.16/0.33  # Proof object clause steps            : 24
% 0.16/0.33  # Proof object formula steps           : 17
% 0.16/0.33  # Proof object conjectures             : 16
% 0.16/0.33  # Proof object clause conjectures      : 13
% 0.16/0.33  # Proof object formula conjectures     : 3
% 0.16/0.33  # Proof object initial clauses used    : 9
% 0.16/0.33  # Proof object initial formulas used   : 8
% 0.16/0.33  # Proof object generating inferences   : 6
% 0.16/0.33  # Proof object simplifying inferences  : 14
% 0.16/0.33  # Training examples: 0 positive, 0 negative
% 0.16/0.33  # Parsed axioms                        : 8
% 0.16/0.33  # Removed by relevancy pruning/SinE    : 0
% 0.16/0.33  # Initial clauses                      : 9
% 0.16/0.33  # Removed in clause preprocessing      : 2
% 0.16/0.33  # Initial clauses in saturation        : 7
% 0.16/0.33  # Processed clauses                    : 24
% 0.16/0.33  # ...of these trivial                  : 0
% 0.16/0.33  # ...subsumed                          : 0
% 0.16/0.33  # ...remaining for further processing  : 24
% 0.16/0.33  # Other redundant clauses eliminated   : 0
% 0.16/0.33  # Clauses deleted for lack of memory   : 0
% 0.16/0.33  # Backward-subsumed                    : 0
% 0.16/0.33  # Backward-rewritten                   : 4
% 0.16/0.33  # Generated clauses                    : 14
% 0.16/0.33  # ...of the previous two non-trivial   : 14
% 0.16/0.33  # Contextual simplify-reflections      : 0
% 0.16/0.33  # Paramodulations                      : 14
% 0.16/0.33  # Factorizations                       : 0
% 0.16/0.33  # Equation resolutions                 : 0
% 0.16/0.33  # Propositional unsat checks           : 0
% 0.16/0.33  #    Propositional check models        : 0
% 0.16/0.33  #    Propositional check unsatisfiable : 0
% 0.16/0.33  #    Propositional clauses             : 0
% 0.16/0.33  #    Propositional clauses after purity: 0
% 0.16/0.33  #    Propositional unsat core size     : 0
% 0.16/0.33  #    Propositional preprocessing time  : 0.000
% 0.16/0.33  #    Propositional encoding time       : 0.000
% 0.16/0.33  #    Propositional solver time         : 0.000
% 0.16/0.33  #    Success case prop preproc time    : 0.000
% 0.16/0.33  #    Success case prop encoding time   : 0.000
% 0.16/0.33  #    Success case prop solver time     : 0.000
% 0.16/0.33  # Current number of processed clauses  : 13
% 0.16/0.33  #    Positive orientable unit clauses  : 9
% 0.16/0.33  #    Positive unorientable unit clauses: 0
% 0.16/0.33  #    Negative unit clauses             : 0
% 0.16/0.33  #    Non-unit-clauses                  : 4
% 0.16/0.33  # Current number of unprocessed clauses: 4
% 0.16/0.33  # ...number of literals in the above   : 4
% 0.16/0.33  # Current number of archived formulas  : 0
% 0.16/0.33  # Current number of archived clauses   : 13
% 0.16/0.33  # Clause-clause subsumption calls (NU) : 4
% 0.16/0.33  # Rec. Clause-clause subsumption calls : 4
% 0.16/0.33  # Non-unit clause-clause subsumptions  : 0
% 0.16/0.33  # Unit Clause-clause subsumption calls : 0
% 0.16/0.33  # Rewrite failures with RHS unbound    : 0
% 0.16/0.33  # BW rewrite match attempts            : 4
% 0.16/0.33  # BW rewrite match successes           : 4
% 0.16/0.33  # Condensation attempts                : 0
% 0.16/0.33  # Condensation successes               : 0
% 0.16/0.33  # Termbank termtop insertions          : 921
% 0.16/0.33  
% 0.16/0.33  # -------------------------------------------------
% 0.16/0.33  # User time                : 0.026 s
% 0.16/0.33  # System time              : 0.004 s
% 0.16/0.33  # Total time               : 0.030 s
% 0.16/0.33  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
