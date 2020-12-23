%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1087+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:01 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   34 (  59 expanded)
%              Number of clauses        :   15 (  23 expanded)
%              Number of leaves         :    9 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   41 (  69 expanded)
%              Number of equality atoms :   22 (  44 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT006+2.ax',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t70_enumset1)).

fof(t15_finset_1,conjecture,(
    ! [X1,X2] :
      ( v1_finset_1(X1)
     => v1_finset_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_finset_1)).

fof(fc11_finset_1,axiom,(
    ! [X1,X2] :
      ( v1_finset_1(X1)
     => v1_finset_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_finset_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t75_enumset1)).

fof(c_0_9,plain,(
    ! [X2283,X2284] : k1_setfam_1(k2_tarski(X2283,X2284)) = k3_xboole_0(X2283,X2284) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_10,plain,(
    ! [X2267,X2268] : k1_enumset1(X2267,X2267,X2268) = k2_tarski(X2267,X2268) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_finset_1(X1)
       => v1_finset_1(k3_xboole_0(X1,X2)) ) ),
    inference(assume_negation,[status(cth)],[t15_finset_1])).

fof(c_0_12,plain,(
    ! [X20,X21] :
      ( ~ v1_finset_1(X20)
      | v1_finset_1(k3_xboole_0(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc11_finset_1])])).

cnf(c_0_13,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X3158,X3159,X3160] : k2_enumset1(X3158,X3158,X3159,X3160) = k1_enumset1(X3158,X3159,X3160) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_16,plain,(
    ! [X3308,X3309,X3310,X3311] : k3_enumset1(X3308,X3308,X3309,X3310,X3311) = k2_enumset1(X3308,X3309,X3310,X3311) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_17,plain,(
    ! [X4378,X4379,X4380,X4381,X4382] : k4_enumset1(X4378,X4378,X4379,X4380,X4381,X4382) = k3_enumset1(X4378,X4379,X4380,X4381,X4382) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_18,plain,(
    ! [X4434,X4435,X4436,X4437,X4438,X4439] : k5_enumset1(X4434,X4434,X4435,X4436,X4437,X4438,X4439) = k4_enumset1(X4434,X4435,X4436,X4437,X4438,X4439) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_19,plain,(
    ! [X4511,X4512,X4513,X4514,X4515,X4516,X4517] : k6_enumset1(X4511,X4511,X4512,X4513,X4514,X4515,X4516,X4517) = k5_enumset1(X4511,X4512,X4513,X4514,X4515,X4516,X4517) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_20,negated_conjecture,
    ( v1_finset_1(esk1_0)
    & ~ v1_finset_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_21,plain,
    ( v1_finset_1(k3_xboole_0(X1,X2))
    | ~ v1_finset_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( ~ v1_finset_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( v1_finset_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
    | ~ v1_finset_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( v1_finset_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_finset_1(k1_setfam_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( v1_finset_1(k1_setfam_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,X1))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
