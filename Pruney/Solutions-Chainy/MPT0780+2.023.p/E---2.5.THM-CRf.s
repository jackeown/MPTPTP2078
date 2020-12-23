%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:51 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 421 expanded)
%              Number of clauses        :   53 ( 179 expanded)
%              Number of leaves         :   20 ( 116 expanded)
%              Depth                    :   17
%              Number of atoms          :  158 ( 695 expanded)
%              Number of equality atoms :   77 ( 341 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t29_wellord1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k2_wellord1(k2_wellord1(X3,X2),X1) = k2_wellord1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t43_funct_1,axiom,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(t125_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k8_relat_1(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(t17_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(X2,X1) = k7_relat_1(k8_relat_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_wellord1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(t26_wellord1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k2_wellord1(k2_wellord1(X3,X1),X2) = k2_wellord1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).

fof(t27_wellord1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k2_wellord1(k2_wellord1(X3,X1),X2) = k2_wellord1(k2_wellord1(X3,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(X1,X2)
         => k2_wellord1(k2_wellord1(X3,X2),X1) = k2_wellord1(X3,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t29_wellord1])).

fof(c_0_21,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | ~ r1_tarski(X13,X14)
      | r1_tarski(X12,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_22,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & r1_tarski(esk1_0,esk2_0)
    & k2_wellord1(k2_wellord1(esk3_0,esk2_0),esk1_0) != k2_wellord1(esk3_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_23,plain,(
    ! [X42,X43] : k1_setfam_1(k2_tarski(X42,X43)) = k3_xboole_0(X42,X43) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_24,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_27,plain,(
    ! [X10,X11] : r1_tarski(k3_xboole_0(X10,X11),X10) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_28,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X17,X18,X19] : k2_enumset1(X17,X17,X18,X19) = k1_enumset1(X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_31,plain,(
    ! [X20,X21,X22,X23] : k3_enumset1(X20,X20,X21,X22,X23) = k2_enumset1(X20,X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_32,plain,(
    ! [X24,X25,X26,X27,X28] : k4_enumset1(X24,X24,X25,X26,X27,X28) = k3_enumset1(X24,X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_33,plain,(
    ! [X29,X30,X31,X32,X33,X34] : k5_enumset1(X29,X29,X30,X31,X32,X33,X34) = k4_enumset1(X29,X30,X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_34,plain,(
    ! [X35,X36,X37,X38,X39,X40,X41] : k6_enumset1(X35,X35,X36,X37,X38,X39,X40,X41) = k5_enumset1(X35,X36,X37,X38,X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_36,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_43,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_44,plain,(
    ! [X52,X53] : k5_relat_1(k6_relat_1(X53),k6_relat_1(X52)) = k6_relat_1(k3_xboole_0(X52,X53)) ),
    inference(variable_rename,[status(thm)],[t43_funct_1])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X2,esk1_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_35])).

cnf(c_0_46,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_48,plain,(
    ! [X47] :
      ( k1_relat_1(k6_relat_1(X47)) = X47
      & k2_relat_1(k6_relat_1(X47)) = X47 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_49,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k3_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_50,plain,(
    ! [X45,X46] :
      ( ~ v1_relat_1(X46)
      | ~ r1_tarski(k2_relat_1(X46),X45)
      | k8_relat_1(X45,X46) = X46 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,k1_setfam_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,X2))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_53,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_55,plain,
    ( k8_relat_1(X2,X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_56,plain,(
    ! [X44] : v1_relat_1(k6_relat_1(X44)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k1_setfam_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,X1)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

fof(c_0_59,plain,(
    ! [X48,X49] :
      ( ~ v1_relat_1(X49)
      | k7_relat_1(X49,X48) = k5_relat_1(k6_relat_1(X48),X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_60,plain,(
    ! [X54,X55] :
      ( ~ v1_relat_1(X55)
      | k2_wellord1(X55,X54) = k7_relat_1(k8_relat_1(X54,X55),X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_wellord1])])).

cnf(c_0_61,negated_conjecture,
    ( k8_relat_1(esk2_0,X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),esk1_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_35])).

cnf(c_0_62,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(esk1_0))),esk2_0) ),
    inference(rw,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_64,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_65,plain,
    ( k2_wellord1(X1,X2) = k7_relat_1(k8_relat_1(X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( k8_relat_1(esk2_0,k6_relat_1(X1)) = k6_relat_1(X1)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_53]),c_0_62])])).

fof(c_0_67,plain,(
    ! [X50,X51] :
      ( ~ v1_relat_1(X51)
      | ~ r1_tarski(k1_relat_1(X51),X50)
      | k7_relat_1(X51,X50) = X51 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(esk1_0),X1)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_62])])).

cnf(c_0_69,negated_conjecture,
    ( k7_relat_1(k6_relat_1(X1),esk2_0) = k2_wellord1(k6_relat_1(X1),esk2_0)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_62])])).

cnf(c_0_70,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_71,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_72,plain,
    ( k8_relat_1(X1,k6_relat_1(X2)) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_53]),c_0_62])])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k2_relat_1(k2_wellord1(k6_relat_1(esk1_0),esk2_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_52])])).

cnf(c_0_74,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_62])])).

cnf(c_0_75,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k2_wellord1(k6_relat_1(X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_72]),c_0_62])])).

fof(c_0_76,plain,(
    ! [X56,X57,X58] :
      ( ~ v1_relat_1(X58)
      | k2_wellord1(k2_wellord1(X58,X56),X57) = k2_wellord1(X58,k3_xboole_0(X56,X57)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_wellord1])])).

cnf(c_0_77,negated_conjecture,
    ( k8_relat_1(esk2_0,k2_wellord1(k6_relat_1(esk1_0),esk2_0)) = k2_wellord1(k6_relat_1(esk1_0),esk2_0)
    | ~ v1_relat_1(k2_wellord1(k6_relat_1(esk1_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_73])).

cnf(c_0_78,plain,
    ( k2_wellord1(k6_relat_1(X1),X2) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_79,plain,
    ( k2_wellord1(k2_wellord1(X1,X2),X3) = k2_wellord1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_80,negated_conjecture,
    ( k8_relat_1(esk2_0,k6_relat_1(esk1_0)) = k6_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_62]),c_0_26])])).

cnf(c_0_81,plain,
    ( k2_wellord1(k2_wellord1(X1,X2),X3) = k2_wellord1(X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_82,negated_conjecture,
    ( k7_relat_1(k6_relat_1(esk1_0),esk2_0) = k2_wellord1(k6_relat_1(esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_80]),c_0_62])])).

fof(c_0_83,plain,(
    ! [X59,X60,X61] :
      ( ~ v1_relat_1(X61)
      | k2_wellord1(k2_wellord1(X61,X59),X60) = k2_wellord1(k2_wellord1(X61,X60),X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_wellord1])])).

cnf(c_0_84,plain,
    ( k2_wellord1(X1,k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))) = k2_wellord1(k2_wellord1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_81,c_0_58])).

cnf(c_0_85,negated_conjecture,
    ( k2_wellord1(k6_relat_1(esk1_0),esk2_0) = k6_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_82]),c_0_26])])).

cnf(c_0_86,negated_conjecture,
    ( k2_wellord1(k2_wellord1(esk3_0,esk2_0),esk1_0) != k2_wellord1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_87,plain,
    ( k2_wellord1(k2_wellord1(X1,X2),X3) = k2_wellord1(k2_wellord1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_88,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_89,plain,
    ( k2_wellord1(X1,k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k2_wellord1(k2_wellord1(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_64]),c_0_62])])).

cnf(c_0_90,negated_conjecture,
    ( k7_relat_1(k6_relat_1(esk1_0),esk2_0) = k6_relat_1(esk1_0) ),
    inference(rw,[status(thm)],[c_0_82,c_0_85])).

cnf(c_0_91,negated_conjecture,
    ( k2_wellord1(k2_wellord1(esk3_0,esk1_0),esk2_0) != k2_wellord1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88])])).

cnf(c_0_92,negated_conjecture,
    ( k2_wellord1(k2_wellord1(X1,esk1_0),esk2_0) = k2_wellord1(X1,esk1_0)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_53])).

cnf(c_0_93,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_88])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:05:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.027 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t29_wellord1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k2_wellord1(k2_wellord1(X3,X2),X1)=k2_wellord1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_wellord1)).
% 0.19/0.40  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.19/0.40  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.40  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.19/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.40  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.40  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.40  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.40  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.19/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.40  fof(t43_funct_1, axiom, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 0.19/0.40  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.19/0.40  fof(t125_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k8_relat_1(X1,X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 0.19/0.40  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.19/0.40  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.19/0.40  fof(t17_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_wellord1(X2,X1)=k7_relat_1(k8_relat_1(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_wellord1)).
% 0.19/0.40  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 0.19/0.40  fof(t26_wellord1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k2_wellord1(k2_wellord1(X3,X1),X2)=k2_wellord1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_wellord1)).
% 0.19/0.40  fof(t27_wellord1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k2_wellord1(k2_wellord1(X3,X1),X2)=k2_wellord1(k2_wellord1(X3,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_wellord1)).
% 0.19/0.40  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k2_wellord1(k2_wellord1(X3,X2),X1)=k2_wellord1(X3,X1)))), inference(assume_negation,[status(cth)],[t29_wellord1])).
% 0.19/0.40  fof(c_0_21, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|~r1_tarski(X13,X14)|r1_tarski(X12,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.19/0.40  fof(c_0_22, negated_conjecture, (v1_relat_1(esk3_0)&(r1_tarski(esk1_0,esk2_0)&k2_wellord1(k2_wellord1(esk3_0,esk2_0),esk1_0)!=k2_wellord1(esk3_0,esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.19/0.40  fof(c_0_23, plain, ![X42, X43]:k1_setfam_1(k2_tarski(X42,X43))=k3_xboole_0(X42,X43), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.40  fof(c_0_24, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.40  cnf(c_0_25, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.40  cnf(c_0_26, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.40  fof(c_0_27, plain, ![X10, X11]:r1_tarski(k3_xboole_0(X10,X11),X10), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.19/0.40  cnf(c_0_28, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.40  cnf(c_0_29, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.40  fof(c_0_30, plain, ![X17, X18, X19]:k2_enumset1(X17,X17,X18,X19)=k1_enumset1(X17,X18,X19), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.40  fof(c_0_31, plain, ![X20, X21, X22, X23]:k3_enumset1(X20,X20,X21,X22,X23)=k2_enumset1(X20,X21,X22,X23), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.40  fof(c_0_32, plain, ![X24, X25, X26, X27, X28]:k4_enumset1(X24,X24,X25,X26,X27,X28)=k3_enumset1(X24,X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.40  fof(c_0_33, plain, ![X29, X30, X31, X32, X33, X34]:k5_enumset1(X29,X29,X30,X31,X32,X33,X34)=k4_enumset1(X29,X30,X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.40  fof(c_0_34, plain, ![X35, X36, X37, X38, X39, X40, X41]:k6_enumset1(X35,X35,X36,X37,X38,X39,X40,X41)=k5_enumset1(X35,X36,X37,X38,X39,X40,X41), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.19/0.40  cnf(c_0_35, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.40  cnf(c_0_36, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.40  cnf(c_0_37, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.40  cnf(c_0_38, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.40  cnf(c_0_39, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.40  cnf(c_0_40, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.40  cnf(c_0_41, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.40  cnf(c_0_42, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.40  fof(c_0_43, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.40  fof(c_0_44, plain, ![X52, X53]:k5_relat_1(k6_relat_1(X53),k6_relat_1(X52))=k6_relat_1(k3_xboole_0(X52,X53)), inference(variable_rename,[status(thm)],[t43_funct_1])).
% 0.19/0.40  cnf(c_0_45, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X2,esk1_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_25, c_0_35])).
% 0.19/0.40  cnf(c_0_46, plain, (r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.19/0.40  cnf(c_0_47, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.40  fof(c_0_48, plain, ![X47]:(k1_relat_1(k6_relat_1(X47))=X47&k2_relat_1(k6_relat_1(X47))=X47), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.19/0.40  cnf(c_0_49, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k3_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.40  fof(c_0_50, plain, ![X45, X46]:(~v1_relat_1(X46)|(~r1_tarski(k2_relat_1(X46),X45)|k8_relat_1(X45,X46)=X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).
% 0.19/0.40  cnf(c_0_51, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,k1_setfam_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,X2)))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.40  cnf(c_0_52, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_47])).
% 0.19/0.40  cnf(c_0_53, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.40  cnf(c_0_54, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.19/0.40  cnf(c_0_55, plain, (k8_relat_1(X2,X1)=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.40  fof(c_0_56, plain, ![X44]:v1_relat_1(k6_relat_1(X44)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.19/0.40  cnf(c_0_57, negated_conjecture, (r1_tarski(k1_setfam_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,X1)),esk2_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.40  cnf(c_0_58, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.40  fof(c_0_59, plain, ![X48, X49]:(~v1_relat_1(X49)|k7_relat_1(X49,X48)=k5_relat_1(k6_relat_1(X48),X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.19/0.40  fof(c_0_60, plain, ![X54, X55]:(~v1_relat_1(X55)|k2_wellord1(X55,X54)=k7_relat_1(k8_relat_1(X54,X55),X54)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_wellord1])])).
% 0.19/0.40  cnf(c_0_61, negated_conjecture, (k8_relat_1(esk2_0,X1)=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),esk1_0)), inference(spm,[status(thm)],[c_0_55, c_0_35])).
% 0.19/0.40  cnf(c_0_62, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.40  cnf(c_0_63, negated_conjecture, (r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(esk1_0))),esk2_0)), inference(rw,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.40  cnf(c_0_64, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.40  cnf(c_0_65, plain, (k2_wellord1(X1,X2)=k7_relat_1(k8_relat_1(X2,X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.40  cnf(c_0_66, negated_conjecture, (k8_relat_1(esk2_0,k6_relat_1(X1))=k6_relat_1(X1)|~r1_tarski(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_53]), c_0_62])])).
% 0.19/0.40  fof(c_0_67, plain, ![X50, X51]:(~v1_relat_1(X51)|(~r1_tarski(k1_relat_1(X51),X50)|k7_relat_1(X51,X50)=X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.19/0.40  cnf(c_0_68, negated_conjecture, (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(esk1_0),X1)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_62])])).
% 0.19/0.40  cnf(c_0_69, negated_conjecture, (k7_relat_1(k6_relat_1(X1),esk2_0)=k2_wellord1(k6_relat_1(X1),esk2_0)|~r1_tarski(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_62])])).
% 0.19/0.40  cnf(c_0_70, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.40  cnf(c_0_71, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.40  cnf(c_0_72, plain, (k8_relat_1(X1,k6_relat_1(X2))=k6_relat_1(X2)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_53]), c_0_62])])).
% 0.19/0.40  cnf(c_0_73, negated_conjecture, (r1_tarski(k2_relat_1(k2_wellord1(k6_relat_1(esk1_0),esk2_0)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_52])])).
% 0.19/0.40  cnf(c_0_74, plain, (k7_relat_1(k6_relat_1(X1),X2)=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_62])])).
% 0.19/0.40  cnf(c_0_75, plain, (k7_relat_1(k6_relat_1(X1),X2)=k2_wellord1(k6_relat_1(X1),X2)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_72]), c_0_62])])).
% 0.19/0.40  fof(c_0_76, plain, ![X56, X57, X58]:(~v1_relat_1(X58)|k2_wellord1(k2_wellord1(X58,X56),X57)=k2_wellord1(X58,k3_xboole_0(X56,X57))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_wellord1])])).
% 0.19/0.40  cnf(c_0_77, negated_conjecture, (k8_relat_1(esk2_0,k2_wellord1(k6_relat_1(esk1_0),esk2_0))=k2_wellord1(k6_relat_1(esk1_0),esk2_0)|~v1_relat_1(k2_wellord1(k6_relat_1(esk1_0),esk2_0))), inference(spm,[status(thm)],[c_0_55, c_0_73])).
% 0.19/0.40  cnf(c_0_78, plain, (k2_wellord1(k6_relat_1(X1),X2)=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.19/0.40  cnf(c_0_79, plain, (k2_wellord1(k2_wellord1(X1,X2),X3)=k2_wellord1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.19/0.40  cnf(c_0_80, negated_conjecture, (k8_relat_1(esk2_0,k6_relat_1(esk1_0))=k6_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_62]), c_0_26])])).
% 0.19/0.40  cnf(c_0_81, plain, (k2_wellord1(k2_wellord1(X1,X2),X3)=k2_wellord1(X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.19/0.40  cnf(c_0_82, negated_conjecture, (k7_relat_1(k6_relat_1(esk1_0),esk2_0)=k2_wellord1(k6_relat_1(esk1_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_80]), c_0_62])])).
% 0.19/0.40  fof(c_0_83, plain, ![X59, X60, X61]:(~v1_relat_1(X61)|k2_wellord1(k2_wellord1(X61,X59),X60)=k2_wellord1(k2_wellord1(X61,X60),X59)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_wellord1])])).
% 0.19/0.40  cnf(c_0_84, plain, (k2_wellord1(X1,k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))))=k2_wellord1(k2_wellord1(X1,X3),X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_81, c_0_58])).
% 0.19/0.40  cnf(c_0_85, negated_conjecture, (k2_wellord1(k6_relat_1(esk1_0),esk2_0)=k6_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_82]), c_0_26])])).
% 0.19/0.40  cnf(c_0_86, negated_conjecture, (k2_wellord1(k2_wellord1(esk3_0,esk2_0),esk1_0)!=k2_wellord1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.40  cnf(c_0_87, plain, (k2_wellord1(k2_wellord1(X1,X2),X3)=k2_wellord1(k2_wellord1(X1,X3),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.19/0.40  cnf(c_0_88, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.40  cnf(c_0_89, plain, (k2_wellord1(X1,k2_relat_1(k7_relat_1(k6_relat_1(X2),X3)))=k2_wellord1(k2_wellord1(X1,X2),X3)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_64]), c_0_62])])).
% 0.19/0.40  cnf(c_0_90, negated_conjecture, (k7_relat_1(k6_relat_1(esk1_0),esk2_0)=k6_relat_1(esk1_0)), inference(rw,[status(thm)],[c_0_82, c_0_85])).
% 0.19/0.40  cnf(c_0_91, negated_conjecture, (k2_wellord1(k2_wellord1(esk3_0,esk1_0),esk2_0)!=k2_wellord1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88])])).
% 0.19/0.40  cnf(c_0_92, negated_conjecture, (k2_wellord1(k2_wellord1(X1,esk1_0),esk2_0)=k2_wellord1(X1,esk1_0)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_53])).
% 0.19/0.40  cnf(c_0_93, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_88])]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 94
% 0.19/0.40  # Proof object clause steps            : 53
% 0.19/0.40  # Proof object formula steps           : 41
% 0.19/0.40  # Proof object conjectures             : 24
% 0.19/0.40  # Proof object clause conjectures      : 21
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 23
% 0.19/0.40  # Proof object initial formulas used   : 20
% 0.19/0.40  # Proof object generating inferences   : 22
% 0.19/0.40  # Proof object simplifying inferences  : 51
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 20
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 25
% 0.19/0.40  # Removed in clause preprocessing      : 7
% 0.19/0.40  # Initial clauses in saturation        : 18
% 0.19/0.40  # Processed clauses                    : 342
% 0.19/0.40  # ...of these trivial                  : 6
% 0.19/0.40  # ...subsumed                          : 175
% 0.19/0.40  # ...remaining for further processing  : 161
% 0.19/0.40  # Other redundant clauses eliminated   : 2
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 1
% 0.19/0.40  # Backward-rewritten                   : 15
% 0.19/0.40  # Generated clauses                    : 1321
% 0.19/0.40  # ...of the previous two non-trivial   : 1057
% 0.19/0.40  # Contextual simplify-reflections      : 0
% 0.19/0.40  # Paramodulations                      : 1319
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 2
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 126
% 0.19/0.40  #    Positive orientable unit clauses  : 40
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 2
% 0.19/0.40  #    Non-unit-clauses                  : 84
% 0.19/0.40  # Current number of unprocessed clauses: 708
% 0.19/0.40  # ...number of literals in the above   : 1674
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 40
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 2284
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 1717
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 175
% 0.19/0.40  # Unit Clause-clause subsumption calls : 6
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 24
% 0.19/0.40  # BW rewrite match successes           : 6
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 20966
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.052 s
% 0.19/0.40  # System time              : 0.005 s
% 0.19/0.40  # Total time               : 0.058 s
% 0.19/0.40  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
