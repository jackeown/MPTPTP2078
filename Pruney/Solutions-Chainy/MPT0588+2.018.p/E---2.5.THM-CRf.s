%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:03 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   37 (  76 expanded)
%              Number of clauses        :   18 (  32 expanded)
%              Number of leaves         :    9 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   52 (  96 expanded)
%              Number of equality atoms :   34 (  72 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t192_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k7_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t189_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(X1,k1_relat_1(X2)) = k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => k7_relat_1(X2,X1) = k7_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1)) ) ),
    inference(assume_negation,[status(cth)],[t192_relat_1])).

fof(c_0_10,plain,(
    ! [X11,X12] : k1_setfam_1(k2_tarski(X11,X12)) = k3_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_11,plain,(
    ! [X6,X7] : k1_enumset1(X6,X6,X7) = k2_tarski(X6,X7) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & k7_relat_1(esk2_0,esk1_0) != k7_relat_1(esk2_0,k3_xboole_0(k1_relat_1(esk2_0),esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_13,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X8,X9,X10] : k2_enumset1(X8,X8,X9,X10) = k1_enumset1(X8,X9,X10) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_16,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_17,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X18)
      | k1_relat_1(k7_relat_1(X18,X17)) = k3_xboole_0(k1_relat_1(X18),X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

cnf(c_0_18,negated_conjecture,
    ( k7_relat_1(esk2_0,esk1_0) != k7_relat_1(esk2_0,k3_xboole_0(k1_relat_1(esk2_0),esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X16] :
      ( k1_relat_1(k6_relat_1(X16)) = X16
      & k2_relat_1(k6_relat_1(X16)) = X16 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_24,plain,(
    ! [X13] : v1_relat_1(k6_relat_1(X13)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_25,negated_conjecture,
    ( k7_relat_1(esk2_0,esk1_0) != k7_relat_1(esk2_0,k1_setfam_1(k2_enumset1(k1_relat_1(esk2_0),k1_relat_1(esk2_0),k1_relat_1(esk2_0),esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_26,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k1_setfam_1(k2_enumset1(X2,X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_19]),c_0_19]),c_0_20]),c_0_20])).

cnf(c_0_27,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_19]),c_0_20])).

cnf(c_0_28,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( k7_relat_1(esk2_0,k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,k1_relat_1(esk2_0)))) != k7_relat_1(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

fof(c_0_32,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X14)
      | ~ v1_relat_1(X15)
      | k7_relat_1(X14,k1_relat_1(X15)) = k7_relat_1(X14,k1_relat_1(k7_relat_1(X15,k1_relat_1(X14)))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t189_relat_1])])])).

cnf(c_0_33,negated_conjecture,
    ( k7_relat_1(esk2_0,k1_relat_1(k7_relat_1(k6_relat_1(esk1_0),k1_relat_1(esk2_0)))) != k7_relat_1(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,plain,
    ( k7_relat_1(X1,k1_relat_1(X2)) = k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_28]),c_0_29]),c_0_35])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:34:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.36  #
% 0.19/0.36  # Preprocessing time       : 0.027 s
% 0.19/0.36  # Presaturation interreduction done
% 0.19/0.36  
% 0.19/0.36  # Proof found!
% 0.19/0.36  # SZS status Theorem
% 0.19/0.36  # SZS output start CNFRefutation
% 0.19/0.36  fof(t192_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k7_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 0.19/0.36  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.36  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.36  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.36  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.36  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 0.19/0.36  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.19/0.36  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.19/0.36  fof(t189_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k7_relat_1(X1,k1_relat_1(X2))=k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_relat_1)).
% 0.19/0.36  fof(c_0_9, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k7_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t192_relat_1])).
% 0.19/0.36  fof(c_0_10, plain, ![X11, X12]:k1_setfam_1(k2_tarski(X11,X12))=k3_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.36  fof(c_0_11, plain, ![X6, X7]:k1_enumset1(X6,X6,X7)=k2_tarski(X6,X7), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.36  fof(c_0_12, negated_conjecture, (v1_relat_1(esk2_0)&k7_relat_1(esk2_0,esk1_0)!=k7_relat_1(esk2_0,k3_xboole_0(k1_relat_1(esk2_0),esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.19/0.36  cnf(c_0_13, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.36  cnf(c_0_14, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.36  fof(c_0_15, plain, ![X8, X9, X10]:k2_enumset1(X8,X8,X9,X10)=k1_enumset1(X8,X9,X10), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.36  fof(c_0_16, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.36  fof(c_0_17, plain, ![X17, X18]:(~v1_relat_1(X18)|k1_relat_1(k7_relat_1(X18,X17))=k3_xboole_0(k1_relat_1(X18),X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.19/0.36  cnf(c_0_18, negated_conjecture, (k7_relat_1(esk2_0,esk1_0)!=k7_relat_1(esk2_0,k3_xboole_0(k1_relat_1(esk2_0),esk1_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.36  cnf(c_0_19, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.36  cnf(c_0_20, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.36  cnf(c_0_21, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.36  cnf(c_0_22, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.36  fof(c_0_23, plain, ![X16]:(k1_relat_1(k6_relat_1(X16))=X16&k2_relat_1(k6_relat_1(X16))=X16), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.19/0.36  fof(c_0_24, plain, ![X13]:v1_relat_1(k6_relat_1(X13)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.19/0.36  cnf(c_0_25, negated_conjecture, (k7_relat_1(esk2_0,esk1_0)!=k7_relat_1(esk2_0,k1_setfam_1(k2_enumset1(k1_relat_1(esk2_0),k1_relat_1(esk2_0),k1_relat_1(esk2_0),esk1_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.19/0.36  cnf(c_0_26, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k1_setfam_1(k2_enumset1(X2,X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_19]), c_0_19]), c_0_20]), c_0_20])).
% 0.19/0.36  cnf(c_0_27, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_19]), c_0_20])).
% 0.19/0.36  cnf(c_0_28, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.36  cnf(c_0_29, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.36  cnf(c_0_30, negated_conjecture, (k7_relat_1(esk2_0,k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,k1_relat_1(esk2_0))))!=k7_relat_1(esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.36  cnf(c_0_31, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.19/0.36  fof(c_0_32, plain, ![X14, X15]:(~v1_relat_1(X14)|(~v1_relat_1(X15)|k7_relat_1(X14,k1_relat_1(X15))=k7_relat_1(X14,k1_relat_1(k7_relat_1(X15,k1_relat_1(X14)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t189_relat_1])])])).
% 0.19/0.36  cnf(c_0_33, negated_conjecture, (k7_relat_1(esk2_0,k1_relat_1(k7_relat_1(k6_relat_1(esk1_0),k1_relat_1(esk2_0))))!=k7_relat_1(esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.36  cnf(c_0_34, plain, (k7_relat_1(X1,k1_relat_1(X2))=k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1))))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.36  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.36  cnf(c_0_36, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_28]), c_0_29]), c_0_35])]), ['proof']).
% 0.19/0.36  # SZS output end CNFRefutation
% 0.19/0.36  # Proof object total steps             : 37
% 0.19/0.36  # Proof object clause steps            : 18
% 0.19/0.36  # Proof object formula steps           : 19
% 0.19/0.36  # Proof object conjectures             : 9
% 0.19/0.36  # Proof object clause conjectures      : 6
% 0.19/0.36  # Proof object formula conjectures     : 3
% 0.19/0.36  # Proof object initial clauses used    : 10
% 0.19/0.36  # Proof object initial formulas used   : 9
% 0.19/0.36  # Proof object generating inferences   : 2
% 0.19/0.36  # Proof object simplifying inferences  : 17
% 0.19/0.36  # Training examples: 0 positive, 0 negative
% 0.19/0.36  # Parsed axioms                        : 9
% 0.19/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.36  # Initial clauses                      : 11
% 0.19/0.36  # Removed in clause preprocessing      : 3
% 0.19/0.36  # Initial clauses in saturation        : 8
% 0.19/0.36  # Processed clauses                    : 19
% 0.19/0.36  # ...of these trivial                  : 0
% 0.19/0.36  # ...subsumed                          : 0
% 0.19/0.36  # ...remaining for further processing  : 19
% 0.19/0.36  # Other redundant clauses eliminated   : 0
% 0.19/0.36  # Clauses deleted for lack of memory   : 0
% 0.19/0.36  # Backward-subsumed                    : 0
% 0.19/0.36  # Backward-rewritten                   : 4
% 0.19/0.36  # Generated clauses                    : 8
% 0.19/0.36  # ...of the previous two non-trivial   : 11
% 0.19/0.36  # Contextual simplify-reflections      : 0
% 0.19/0.36  # Paramodulations                      : 8
% 0.19/0.36  # Factorizations                       : 0
% 0.19/0.36  # Equation resolutions                 : 0
% 0.19/0.36  # Propositional unsat checks           : 0
% 0.19/0.36  #    Propositional check models        : 0
% 0.19/0.36  #    Propositional check unsatisfiable : 0
% 0.19/0.36  #    Propositional clauses             : 0
% 0.19/0.36  #    Propositional clauses after purity: 0
% 0.19/0.36  #    Propositional unsat core size     : 0
% 0.19/0.36  #    Propositional preprocessing time  : 0.000
% 0.19/0.36  #    Propositional encoding time       : 0.000
% 0.19/0.36  #    Propositional solver time         : 0.000
% 0.19/0.36  #    Success case prop preproc time    : 0.000
% 0.19/0.36  #    Success case prop encoding time   : 0.000
% 0.19/0.36  #    Success case prop solver time     : 0.000
% 0.19/0.36  # Current number of processed clauses  : 7
% 0.19/0.36  #    Positive orientable unit clauses  : 5
% 0.19/0.36  #    Positive unorientable unit clauses: 0
% 0.19/0.36  #    Negative unit clauses             : 1
% 0.19/0.36  #    Non-unit-clauses                  : 1
% 0.19/0.36  # Current number of unprocessed clauses: 8
% 0.19/0.36  # ...number of literals in the above   : 15
% 0.19/0.36  # Current number of archived formulas  : 0
% 0.19/0.36  # Current number of archived clauses   : 15
% 0.19/0.36  # Clause-clause subsumption calls (NU) : 0
% 0.19/0.36  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.36  # Unit Clause-clause subsumption calls : 0
% 0.19/0.36  # Rewrite failures with RHS unbound    : 0
% 0.19/0.36  # BW rewrite match attempts            : 12
% 0.19/0.36  # BW rewrite match successes           : 12
% 0.19/0.36  # Condensation attempts                : 0
% 0.19/0.36  # Condensation successes               : 0
% 0.19/0.36  # Termbank termtop insertions          : 735
% 0.19/0.36  
% 0.19/0.36  # -------------------------------------------------
% 0.19/0.36  # User time                : 0.027 s
% 0.19/0.36  # System time              : 0.004 s
% 0.19/0.36  # Total time               : 0.031 s
% 0.19/0.36  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
