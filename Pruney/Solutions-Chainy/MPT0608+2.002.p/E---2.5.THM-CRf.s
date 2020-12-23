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
% DateTime   : Thu Dec  3 10:52:28 EST 2020

% Result     : Theorem 7.68s
% Output     : CNFRefutation 7.68s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 594 expanded)
%              Number of clauses        :   43 ( 233 expanded)
%              Number of leaves         :   18 ( 178 expanded)
%              Depth                    :   11
%              Number of atoms          :  130 ( 685 expanded)
%              Number of equality atoms :   75 ( 586 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t212_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1))) = k6_subset_1(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

fof(t109_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k7_relat_1(X3,X1),k7_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_18,plain,(
    ! [X50,X51] : k1_setfam_1(k2_tarski(X50,X51)) = k3_xboole_0(X50,X51) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_19,plain,(
    ! [X21,X22] : k1_enumset1(X21,X21,X22) = k2_tarski(X21,X22) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_21,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1))) = k6_subset_1(k1_relat_1(X2),X1) ) ),
    inference(assume_negation,[status(cth)],[t212_relat_1])).

fof(c_0_24,plain,(
    ! [X52,X53,X54] :
      ( ~ v1_relat_1(X54)
      | k7_relat_1(X54,k6_subset_1(X52,X53)) = k6_subset_1(k7_relat_1(X54,X52),k7_relat_1(X54,X53)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_relat_1])])).

fof(c_0_25,plain,(
    ! [X48,X49] : k6_subset_1(X48,X49) = k4_xboole_0(X48,X49) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_28,plain,(
    ! [X23,X24,X25] : k2_enumset1(X23,X23,X24,X25) = k1_enumset1(X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_29,plain,(
    ! [X26,X27,X28,X29] : k3_enumset1(X26,X26,X27,X28,X29) = k2_enumset1(X26,X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_30,plain,(
    ! [X30,X31,X32,X33,X34] : k4_enumset1(X30,X30,X31,X32,X33,X34) = k3_enumset1(X30,X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_31,plain,(
    ! [X35,X36,X37,X38,X39,X40] : k5_enumset1(X35,X35,X36,X37,X38,X39,X40) = k4_enumset1(X35,X36,X37,X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_32,plain,(
    ! [X41,X42,X43,X44,X45,X46,X47] : k6_enumset1(X41,X41,X42,X43,X44,X45,X46,X47) = k5_enumset1(X41,X42,X43,X44,X45,X46,X47) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_33,plain,(
    ! [X57,X58] :
      ( ~ v1_relat_1(X58)
      | k1_relat_1(k7_relat_1(X58,X57)) = k3_xboole_0(k1_relat_1(X58),X57) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

fof(c_0_34,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & k1_relat_1(k6_subset_1(esk2_0,k7_relat_1(esk2_0,esk1_0))) != k6_subset_1(k1_relat_1(esk2_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

fof(c_0_35,plain,(
    ! [X19,X20] : k2_tarski(X19,X20) = k2_tarski(X20,X19) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_36,plain,
    ( k7_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k7_relat_1(X1,X2),k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_39,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_44,plain,(
    ! [X61] :
      ( ~ v1_relat_1(X61)
      | k7_relat_1(X61,k1_relat_1(X61)) = X61 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

cnf(c_0_45,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_46,plain,(
    ! [X59,X60] :
      ( ~ v1_relat_1(X60)
      | ~ r1_tarski(X59,k1_relat_1(X60))
      | k1_relat_1(k7_relat_1(X60,X59)) = X59 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

fof(c_0_47,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,X18)) = k3_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_48,negated_conjecture,
    ( k1_relat_1(k6_subset_1(esk2_0,k7_relat_1(esk2_0,esk1_0))) != k6_subset_1(k1_relat_1(esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_49,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_50,plain,
    ( k7_relat_1(X1,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))) = k5_xboole_0(k7_relat_1(X1,X2),k1_setfam_1(k6_enumset1(k7_relat_1(X1,X2),k7_relat_1(X1,X2),k7_relat_1(X1,X2),k7_relat_1(X1,X2),k7_relat_1(X1,X2),k7_relat_1(X1,X2),k7_relat_1(X1,X2),k7_relat_1(X1,X3))))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43])).

cnf(c_0_51,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_27]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_53,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_55,plain,(
    ! [X15,X16] : r1_tarski(k4_xboole_0(X15,X16),X15) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_56,negated_conjecture,
    ( k1_relat_1(k5_xboole_0(esk2_0,k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k7_relat_1(esk2_0,esk1_0))))) != k5_xboole_0(k1_relat_1(esk2_0),k1_setfam_1(k6_enumset1(k1_relat_1(esk2_0),k1_relat_1(esk2_0),k1_relat_1(esk2_0),k1_relat_1(esk2_0),k1_relat_1(esk2_0),k1_relat_1(esk2_0),k1_relat_1(esk2_0),esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43])).

cnf(c_0_57,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_22]),c_0_22]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43])).

cnf(c_0_58,plain,
    ( k7_relat_1(X1,k5_xboole_0(k1_relat_1(X1),k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2)))) = k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k7_relat_1(X1,X2))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k1_relat_1(k7_relat_1(k7_relat_1(X3,X1),X2))
    | ~ v1_relat_1(k7_relat_1(X3,X1))
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,k1_relat_1(X3)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))))) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_27]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43])).

cnf(c_0_61,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( k1_relat_1(k5_xboole_0(esk2_0,k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k7_relat_1(esk2_0,esk1_0))))) != k5_xboole_0(k1_relat_1(esk2_0),k1_setfam_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,k1_relat_1(esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,plain,
    ( k7_relat_1(X1,k5_xboole_0(k1_relat_1(X1),k1_relat_1(k7_relat_1(k7_relat_1(X2,k1_relat_1(X1)),X3)))) = k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k7_relat_1(X1,X3))))
    | ~ v1_relat_1(k7_relat_1(X2,k1_relat_1(X1)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_65,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_66,plain,
    ( k5_xboole_0(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,k5_xboole_0(k1_relat_1(X1),k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2)))))) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_52])).

cnf(c_0_67,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_68,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,k5_xboole_0(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(k7_relat_1(X1,k1_relat_1(esk2_0)),esk1_0))))) != k5_xboole_0(k1_relat_1(esk2_0),k1_setfam_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,k1_relat_1(esk2_0))))
    | ~ v1_relat_1(k7_relat_1(X1,k1_relat_1(esk2_0)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(esk2_0),k1_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])])).

cnf(c_0_69,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_relat_1(X2))) = k1_relat_1(k7_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_57])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_71,plain,
    ( k5_xboole_0(k1_relat_1(X1),k5_xboole_0(k1_relat_1(X1),k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2)))) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_53]),c_0_67])])).

cnf(c_0_72,plain,
    ( k5_xboole_0(k1_relat_1(X1),k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k5_xboole_0(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X2)))))) = k1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_52])).

cnf(c_0_73,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,k5_xboole_0(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(k7_relat_1(X1,k1_relat_1(esk2_0)),esk1_0))))) != k5_xboole_0(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk2_0,esk1_0)))
    | ~ v1_relat_1(k7_relat_1(X1,k1_relat_1(esk2_0)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(esk2_0),k1_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_64])])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_70])).

cnf(c_0_75,plain,
    ( k5_xboole_0(k1_relat_1(X1),k5_xboole_0(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X2)))) = k1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_52])).

cnf(c_0_76,plain,
    ( k5_xboole_0(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,k5_xboole_0(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X2)))))) = k1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_52])).

cnf(c_0_77,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,k5_xboole_0(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk2_0,esk1_0))))) != k5_xboole_0(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk2_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_51]),c_0_64]),c_0_74])])).

cnf(c_0_78,plain,
    ( k1_relat_1(k7_relat_1(X1,k5_xboole_0(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X2))))) = k5_xboole_0(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_64])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:35:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 7.68/7.84  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 7.68/7.84  # and selection function SelectComplexExceptUniqMaxHorn.
% 7.68/7.84  #
% 7.68/7.84  # Preprocessing time       : 0.027 s
% 7.68/7.84  # Presaturation interreduction done
% 7.68/7.84  
% 7.68/7.84  # Proof found!
% 7.68/7.84  # SZS status Theorem
% 7.68/7.84  # SZS output start CNFRefutation
% 7.68/7.84  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 7.68/7.84  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 7.68/7.84  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.68/7.84  fof(t212_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)))=k6_subset_1(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t212_relat_1)).
% 7.68/7.84  fof(t109_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k7_relat_1(X3,X1),k7_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_relat_1)).
% 7.68/7.84  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 7.68/7.84  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 7.68/7.84  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 7.68/7.84  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 7.68/7.84  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 7.68/7.84  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 7.68/7.84  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 7.68/7.84  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.68/7.84  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 7.68/7.84  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 7.68/7.84  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.68/7.84  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.68/7.84  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.68/7.84  fof(c_0_18, plain, ![X50, X51]:k1_setfam_1(k2_tarski(X50,X51))=k3_xboole_0(X50,X51), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 7.68/7.84  fof(c_0_19, plain, ![X21, X22]:k1_enumset1(X21,X21,X22)=k2_tarski(X21,X22), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 7.68/7.84  fof(c_0_20, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 7.68/7.84  cnf(c_0_21, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 7.68/7.84  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 7.68/7.84  fof(c_0_23, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)))=k6_subset_1(k1_relat_1(X2),X1))), inference(assume_negation,[status(cth)],[t212_relat_1])).
% 7.68/7.84  fof(c_0_24, plain, ![X52, X53, X54]:(~v1_relat_1(X54)|k7_relat_1(X54,k6_subset_1(X52,X53))=k6_subset_1(k7_relat_1(X54,X52),k7_relat_1(X54,X53))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_relat_1])])).
% 7.68/7.84  fof(c_0_25, plain, ![X48, X49]:k6_subset_1(X48,X49)=k4_xboole_0(X48,X49), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 7.68/7.84  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 7.68/7.84  cnf(c_0_27, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 7.68/7.84  fof(c_0_28, plain, ![X23, X24, X25]:k2_enumset1(X23,X23,X24,X25)=k1_enumset1(X23,X24,X25), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 7.68/7.84  fof(c_0_29, plain, ![X26, X27, X28, X29]:k3_enumset1(X26,X26,X27,X28,X29)=k2_enumset1(X26,X27,X28,X29), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 7.68/7.84  fof(c_0_30, plain, ![X30, X31, X32, X33, X34]:k4_enumset1(X30,X30,X31,X32,X33,X34)=k3_enumset1(X30,X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 7.68/7.84  fof(c_0_31, plain, ![X35, X36, X37, X38, X39, X40]:k5_enumset1(X35,X35,X36,X37,X38,X39,X40)=k4_enumset1(X35,X36,X37,X38,X39,X40), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 7.68/7.84  fof(c_0_32, plain, ![X41, X42, X43, X44, X45, X46, X47]:k6_enumset1(X41,X41,X42,X43,X44,X45,X46,X47)=k5_enumset1(X41,X42,X43,X44,X45,X46,X47), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 7.68/7.84  fof(c_0_33, plain, ![X57, X58]:(~v1_relat_1(X58)|k1_relat_1(k7_relat_1(X58,X57))=k3_xboole_0(k1_relat_1(X58),X57)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 7.68/7.84  fof(c_0_34, negated_conjecture, (v1_relat_1(esk2_0)&k1_relat_1(k6_subset_1(esk2_0,k7_relat_1(esk2_0,esk1_0)))!=k6_subset_1(k1_relat_1(esk2_0),esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 7.68/7.84  fof(c_0_35, plain, ![X19, X20]:k2_tarski(X19,X20)=k2_tarski(X20,X19), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 7.68/7.84  cnf(c_0_36, plain, (k7_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k7_relat_1(X1,X2),k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 7.68/7.84  cnf(c_0_37, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 7.68/7.84  cnf(c_0_38, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 7.68/7.84  cnf(c_0_39, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 7.68/7.84  cnf(c_0_40, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 7.68/7.84  cnf(c_0_41, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 7.68/7.84  cnf(c_0_42, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 7.68/7.84  cnf(c_0_43, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 7.68/7.84  fof(c_0_44, plain, ![X61]:(~v1_relat_1(X61)|k7_relat_1(X61,k1_relat_1(X61))=X61), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 7.68/7.84  cnf(c_0_45, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 7.68/7.84  fof(c_0_46, plain, ![X59, X60]:(~v1_relat_1(X60)|(~r1_tarski(X59,k1_relat_1(X60))|k1_relat_1(k7_relat_1(X60,X59))=X59)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 7.68/7.84  fof(c_0_47, plain, ![X17, X18]:k4_xboole_0(X17,k4_xboole_0(X17,X18))=k3_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 7.68/7.84  cnf(c_0_48, negated_conjecture, (k1_relat_1(k6_subset_1(esk2_0,k7_relat_1(esk2_0,esk1_0)))!=k6_subset_1(k1_relat_1(esk2_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 7.68/7.84  cnf(c_0_49, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 7.68/7.84  cnf(c_0_50, plain, (k7_relat_1(X1,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))=k5_xboole_0(k7_relat_1(X1,X2),k1_setfam_1(k6_enumset1(k7_relat_1(X1,X2),k7_relat_1(X1,X2),k7_relat_1(X1,X2),k7_relat_1(X1,X2),k7_relat_1(X1,X2),k7_relat_1(X1,X2),k7_relat_1(X1,X2),k7_relat_1(X1,X3))))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43])).
% 7.68/7.84  cnf(c_0_51, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 7.68/7.84  cnf(c_0_52, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_27]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43])).
% 7.68/7.84  cnf(c_0_53, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 7.68/7.84  cnf(c_0_54, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 7.68/7.84  fof(c_0_55, plain, ![X15, X16]:r1_tarski(k4_xboole_0(X15,X16),X15), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 7.68/7.84  cnf(c_0_56, negated_conjecture, (k1_relat_1(k5_xboole_0(esk2_0,k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k7_relat_1(esk2_0,esk1_0)))))!=k5_xboole_0(k1_relat_1(esk2_0),k1_setfam_1(k6_enumset1(k1_relat_1(esk2_0),k1_relat_1(esk2_0),k1_relat_1(esk2_0),k1_relat_1(esk2_0),k1_relat_1(esk2_0),k1_relat_1(esk2_0),k1_relat_1(esk2_0),esk1_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43])).
% 7.68/7.84  cnf(c_0_57, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_22]), c_0_22]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43])).
% 7.68/7.84  cnf(c_0_58, plain, (k7_relat_1(X1,k5_xboole_0(k1_relat_1(X1),k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))))=k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k7_relat_1(X1,X2))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 7.68/7.84  cnf(c_0_59, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k1_relat_1(k7_relat_1(k7_relat_1(X3,X1),X2))|~v1_relat_1(k7_relat_1(X3,X1))|~v1_relat_1(X3)|~r1_tarski(X1,k1_relat_1(X3))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 7.68/7.84  cnf(c_0_60, plain, (k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))))=k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_27]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43])).
% 7.68/7.84  cnf(c_0_61, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 7.68/7.84  cnf(c_0_62, negated_conjecture, (k1_relat_1(k5_xboole_0(esk2_0,k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k7_relat_1(esk2_0,esk1_0)))))!=k5_xboole_0(k1_relat_1(esk2_0),k1_setfam_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,k1_relat_1(esk2_0))))), inference(rw,[status(thm)],[c_0_56, c_0_57])).
% 7.68/7.84  cnf(c_0_63, plain, (k7_relat_1(X1,k5_xboole_0(k1_relat_1(X1),k1_relat_1(k7_relat_1(k7_relat_1(X2,k1_relat_1(X1)),X3))))=k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k7_relat_1(X1,X3))))|~v1_relat_1(k7_relat_1(X2,k1_relat_1(X1)))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 7.68/7.84  cnf(c_0_64, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 7.68/7.84  fof(c_0_65, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 7.68/7.84  cnf(c_0_66, plain, (k5_xboole_0(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,k5_xboole_0(k1_relat_1(X1),k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))))))=k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_60, c_0_52])).
% 7.68/7.84  cnf(c_0_67, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43])).
% 7.68/7.84  cnf(c_0_68, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,k5_xboole_0(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(k7_relat_1(X1,k1_relat_1(esk2_0)),esk1_0)))))!=k5_xboole_0(k1_relat_1(esk2_0),k1_setfam_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,k1_relat_1(esk2_0))))|~v1_relat_1(k7_relat_1(X1,k1_relat_1(esk2_0)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(esk2_0),k1_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])])).
% 7.68/7.84  cnf(c_0_69, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_relat_1(X2)))=k1_relat_1(k7_relat_1(X2,X1))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_52, c_0_57])).
% 7.68/7.84  cnf(c_0_70, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_65])).
% 7.68/7.84  cnf(c_0_71, plain, (k5_xboole_0(k1_relat_1(X1),k5_xboole_0(k1_relat_1(X1),k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))))=k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_53]), c_0_67])])).
% 7.68/7.84  cnf(c_0_72, plain, (k5_xboole_0(k1_relat_1(X1),k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k5_xboole_0(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X2))))))=k1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_60, c_0_52])).
% 7.68/7.84  cnf(c_0_73, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,k5_xboole_0(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(k7_relat_1(X1,k1_relat_1(esk2_0)),esk1_0)))))!=k5_xboole_0(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk2_0,esk1_0)))|~v1_relat_1(k7_relat_1(X1,k1_relat_1(esk2_0)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(esk2_0),k1_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_64])])).
% 7.68/7.84  cnf(c_0_74, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_70])).
% 7.68/7.84  cnf(c_0_75, plain, (k5_xboole_0(k1_relat_1(X1),k5_xboole_0(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X2))))=k1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_71, c_0_52])).
% 7.68/7.84  cnf(c_0_76, plain, (k5_xboole_0(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,k5_xboole_0(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X2))))))=k1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_72, c_0_52])).
% 7.68/7.84  cnf(c_0_77, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,k5_xboole_0(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk2_0,esk1_0)))))!=k5_xboole_0(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk2_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_51]), c_0_64]), c_0_74])])).
% 7.68/7.84  cnf(c_0_78, plain, (k1_relat_1(k7_relat_1(X1,k5_xboole_0(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X2)))))=k5_xboole_0(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 7.68/7.84  cnf(c_0_79, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_64])]), ['proof']).
% 7.68/7.84  # SZS output end CNFRefutation
% 7.68/7.84  # Proof object total steps             : 80
% 7.68/7.84  # Proof object clause steps            : 43
% 7.68/7.84  # Proof object formula steps           : 37
% 7.68/7.84  # Proof object conjectures             : 11
% 7.68/7.84  # Proof object clause conjectures      : 8
% 7.68/7.84  # Proof object formula conjectures     : 3
% 7.68/7.84  # Proof object initial clauses used    : 19
% 7.68/7.84  # Proof object initial formulas used   : 18
% 7.68/7.84  # Proof object generating inferences   : 14
% 7.68/7.84  # Proof object simplifying inferences  : 85
% 7.68/7.84  # Training examples: 0 positive, 0 negative
% 7.68/7.84  # Parsed axioms                        : 20
% 7.68/7.84  # Removed by relevancy pruning/SinE    : 0
% 7.68/7.84  # Initial clauses                      : 23
% 7.68/7.84  # Removed in clause preprocessing      : 9
% 7.68/7.84  # Initial clauses in saturation        : 14
% 7.68/7.84  # Processed clauses                    : 12230
% 7.68/7.84  # ...of these trivial                  : 13
% 7.68/7.84  # ...subsumed                          : 10187
% 7.68/7.84  # ...remaining for further processing  : 2030
% 7.68/7.84  # Other redundant clauses eliminated   : 3
% 7.68/7.84  # Clauses deleted for lack of memory   : 0
% 7.68/7.84  # Backward-subsumed                    : 1075
% 7.68/7.84  # Backward-rewritten                   : 1
% 7.68/7.84  # Generated clauses                    : 333831
% 7.68/7.84  # ...of the previous two non-trivial   : 331163
% 7.68/7.84  # Contextual simplify-reflections      : 36
% 7.68/7.84  # Paramodulations                      : 333828
% 7.68/7.84  # Factorizations                       : 0
% 7.68/7.84  # Equation resolutions                 : 3
% 7.68/7.84  # Propositional unsat checks           : 0
% 7.68/7.84  #    Propositional check models        : 0
% 7.68/7.84  #    Propositional check unsatisfiable : 0
% 7.68/7.84  #    Propositional clauses             : 0
% 7.68/7.84  #    Propositional clauses after purity: 0
% 7.68/7.84  #    Propositional unsat core size     : 0
% 7.68/7.84  #    Propositional preprocessing time  : 0.000
% 7.68/7.84  #    Propositional encoding time       : 0.000
% 7.68/7.84  #    Propositional solver time         : 0.000
% 7.68/7.84  #    Success case prop preproc time    : 0.000
% 7.68/7.84  #    Success case prop encoding time   : 0.000
% 7.68/7.84  #    Success case prop solver time     : 0.000
% 7.68/7.84  # Current number of processed clauses  : 939
% 7.68/7.84  #    Positive orientable unit clauses  : 19
% 7.68/7.84  #    Positive unorientable unit clauses: 1
% 7.68/7.84  #    Negative unit clauses             : 2
% 7.68/7.84  #    Non-unit-clauses                  : 917
% 7.68/7.84  # Current number of unprocessed clauses: 318710
% 7.68/7.84  # ...number of literals in the above   : 2343979
% 7.68/7.84  # Current number of archived formulas  : 0
% 7.68/7.84  # Current number of archived clauses   : 1098
% 7.68/7.84  # Clause-clause subsumption calls (NU) : 1185975
% 7.68/7.84  # Rec. Clause-clause subsumption calls : 91352
% 7.68/7.84  # Non-unit clause-clause subsumptions  : 11277
% 7.68/7.84  # Unit Clause-clause subsumption calls : 51
% 7.68/7.84  # Rewrite failures with RHS unbound    : 0
% 7.68/7.84  # BW rewrite match attempts            : 209
% 7.68/7.84  # BW rewrite match successes           : 14
% 7.68/7.84  # Condensation attempts                : 0
% 7.68/7.84  # Condensation successes               : 0
% 7.68/7.84  # Termbank termtop insertions          : 24574167
% 7.68/7.86  
% 7.68/7.86  # -------------------------------------------------
% 7.68/7.86  # User time                : 7.344 s
% 7.68/7.86  # System time              : 0.171 s
% 7.68/7.86  # Total time               : 7.515 s
% 7.68/7.86  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
