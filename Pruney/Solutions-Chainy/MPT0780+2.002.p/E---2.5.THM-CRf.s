%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:48 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  187 (8264 expanded)
%              Number of clauses        :  134 (3449 expanded)
%              Number of leaves         :   26 (2400 expanded)
%              Depth                    :   24
%              Number of atoms          :  320 (12236 expanded)
%              Number of equality atoms :  129 (6959 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t125_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k8_relat_1(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

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

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(t17_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(X2,X1) = k7_relat_1(k8_relat_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_wellord1)).

fof(t29_wellord1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k2_wellord1(k2_wellord1(X3,X2),X1) = k2_wellord1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).

fof(t20_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),k3_relat_1(X2))
        & r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_wellord1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t26_wellord1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k2_wellord1(k2_wellord1(X3,X1),X2) = k2_wellord1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).

fof(dt_k2_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k2_wellord1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(t43_funct_1,axiom,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(t18_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(X2,X1) = k8_relat_1(X1,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_wellord1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(c_0_26,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_27,plain,(
    ! [X44,X45] : k3_tarski(k2_tarski(X44,X45)) = k2_xboole_0(X44,X45) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_28,plain,(
    ! [X17,X18] : k1_enumset1(X17,X17,X18) = k2_tarski(X17,X18) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_29,plain,(
    ! [X49,X50] :
      ( ~ v1_relat_1(X50)
      | ~ r1_tarski(k2_relat_1(X50),X49)
      | k8_relat_1(X49,X50) = X50 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_31,plain,(
    ! [X13,X14] : r1_tarski(X13,k2_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_32,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_34,plain,(
    ! [X19,X20,X21] : k2_enumset1(X19,X19,X20,X21) = k1_enumset1(X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_35,plain,(
    ! [X22,X23,X24,X25] : k3_enumset1(X22,X22,X23,X24,X25) = k2_enumset1(X22,X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_36,plain,(
    ! [X26,X27,X28,X29,X30] : k4_enumset1(X26,X26,X27,X28,X29,X30) = k3_enumset1(X26,X27,X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_37,plain,(
    ! [X31,X32,X33,X34,X35,X36] : k5_enumset1(X31,X31,X32,X33,X34,X35,X36) = k4_enumset1(X31,X32,X33,X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_38,plain,(
    ! [X37,X38,X39,X40,X41,X42,X43] : k6_enumset1(X37,X37,X38,X39,X40,X41,X42,X43) = k5_enumset1(X37,X38,X39,X40,X41,X42,X43) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_39,plain,
    ( k8_relat_1(X2,X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_30])).

fof(c_0_41,plain,(
    ! [X51] :
      ( k1_relat_1(k6_relat_1(X51)) = X51
      & k2_relat_1(k6_relat_1(X51)) = X51 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_42,plain,(
    ! [X57] :
      ( v1_relat_1(k6_relat_1(X57))
      & v1_funct_1(k6_relat_1(X57)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_43,plain,(
    ! [X56] :
      ( ~ v1_relat_1(X56)
      | k7_relat_1(X56,k1_relat_1(X56)) = X56 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_46,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_51,plain,(
    ! [X48] :
      ( ~ v1_relat_1(X48)
      | k3_relat_1(X48) = k2_xboole_0(k1_relat_1(X48),k2_relat_1(X48)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

fof(c_0_52,plain,(
    ! [X62,X63] :
      ( ~ v1_relat_1(X63)
      | k2_wellord1(X63,X62) = k7_relat_1(k8_relat_1(X62,X63),X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_wellord1])])).

cnf(c_0_53,plain,
    ( k8_relat_1(k2_relat_1(X1),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_54,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_55,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_56,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_57,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_58,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(X1,X2)
         => k2_wellord1(k2_wellord1(X3,X2),X1) = k2_wellord1(X3,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t29_wellord1])).

cnf(c_0_59,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_61,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_62,plain,(
    ! [X66,X67] :
      ( ( r1_tarski(k3_relat_1(k2_wellord1(X67,X66)),k3_relat_1(X67))
        | ~ v1_relat_1(X67) )
      & ( r1_tarski(k3_relat_1(k2_wellord1(X67,X66)),X66)
        | ~ v1_relat_1(X67) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_wellord1])])])).

cnf(c_0_63,plain,
    ( k2_wellord1(X1,X2) = k7_relat_1(k8_relat_1(X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_64,plain,
    ( k8_relat_1(X1,k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])])).

cnf(c_0_65,plain,
    ( k7_relat_1(k6_relat_1(X1),X1) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_55])])).

fof(c_0_66,plain,(
    ! [X46,X47] : k1_setfam_1(k2_tarski(X46,X47)) = k3_xboole_0(X46,X47) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_67,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,X11)
      | ~ r1_tarski(X11,X12)
      | r1_tarski(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_68,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & r1_tarski(esk1_0,esk2_0)
    & k2_wellord1(k2_wellord1(esk3_0,esk2_0),esk1_0) != k2_wellord1(esk3_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_58])])])).

cnf(c_0_69,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = X1
    | ~ r1_tarski(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_70,plain,
    ( k3_relat_1(X1) = k3_tarski(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_71,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_72,plain,
    ( k2_wellord1(k6_relat_1(X1),X1) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_55])])).

fof(c_0_73,plain,(
    ! [X15,X16] : k2_tarski(X15,X16) = k2_tarski(X16,X15) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_74,plain,(
    ! [X68,X69,X70] :
      ( ~ v1_relat_1(X70)
      | k2_wellord1(k2_wellord1(X70,X68),X69) = k2_wellord1(X70,k3_xboole_0(X68,X69)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_wellord1])])).

cnf(c_0_75,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_78,plain,
    ( k3_relat_1(X1) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k3_relat_1(X1),k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_79,plain,
    ( r1_tarski(k3_relat_1(k6_relat_1(X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_55])])).

cnf(c_0_80,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

fof(c_0_81,plain,(
    ! [X60,X61] :
      ( ~ v1_relat_1(X60)
      | v1_relat_1(k2_wellord1(X60,X61)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).

cnf(c_0_82,plain,
    ( k2_wellord1(k2_wellord1(X1,X2),X3) = k2_wellord1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_83,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_75,c_0_33])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_85,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X1,X2)),k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_86,plain,
    ( k3_relat_1(k6_relat_1(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_57]),c_0_55]),c_0_79])])).

cnf(c_0_87,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_33]),c_0_33]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_50]),c_0_50])).

cnf(c_0_88,plain,
    ( v1_relat_1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_89,plain,
    ( k2_wellord1(k2_wellord1(X1,X2),X3) = k2_wellord1(X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_83]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X2,esk1_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_76,c_0_84])).

fof(c_0_91,plain,(
    ! [X58,X59] : k5_relat_1(k6_relat_1(X59),k6_relat_1(X58)) = k6_relat_1(k3_xboole_0(X58,X59)) ),
    inference(variable_rename,[status(thm)],[t43_funct_1])).

cnf(c_0_92,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(k6_relat_1(X1),X2)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_55])])).

cnf(c_0_93,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_87])).

cnf(c_0_94,plain,
    ( v1_relat_1(k2_wellord1(k2_wellord1(X1,X2),X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

fof(c_0_95,plain,(
    ! [X54,X55] :
      ( ~ v1_relat_1(X55)
      | ~ r1_tarski(k1_relat_1(X55),X54)
      | k7_relat_1(X55,X54) = X55 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k3_relat_1(k2_wellord1(X2,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_90,c_0_71])).

cnf(c_0_97,plain,
    ( r1_tarski(k1_relat_1(X1),k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_70])).

cnf(c_0_98,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k3_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_99,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_relat_1(k2_wellord1(k6_relat_1(X2),X3))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_92])).

cnf(c_0_100,plain,
    ( r1_tarski(k2_relat_1(X1),k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_93,c_0_70])).

cnf(c_0_101,plain,
    ( v1_relat_1(k2_wellord1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_72]),c_0_55])])).

fof(c_0_102,plain,(
    ! [X64,X65] :
      ( ~ v1_relat_1(X65)
      | k2_wellord1(X65,X64) = k8_relat_1(X64,k7_relat_1(X65,X64)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_wellord1])])).

cnf(c_0_103,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(k1_relat_1(k2_wellord1(X1,esk1_0)),esk2_0)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_88])).

cnf(c_0_105,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_83]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_106,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,k3_relat_1(k2_wellord1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_71])).

cnf(c_0_107,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(k6_relat_1(X1),X2)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_101])])).

cnf(c_0_108,plain,
    ( r1_tarski(k1_relat_1(k2_wellord1(k6_relat_1(X1),X2)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_97]),c_0_101])])).

cnf(c_0_109,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,k3_relat_1(k6_relat_1(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_72]),c_0_55])])).

cnf(c_0_110,negated_conjecture,
    ( k8_relat_1(esk2_0,X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),esk1_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_84])).

cnf(c_0_111,plain,
    ( k2_wellord1(X1,X2) = k8_relat_1(X2,k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_112,negated_conjecture,
    ( k7_relat_1(k2_wellord1(X1,esk1_0),esk2_0) = k2_wellord1(X1,esk1_0)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_88])).

cnf(c_0_113,negated_conjecture,
    ( r1_tarski(k2_relat_1(k2_wellord1(X1,esk1_0)),esk2_0)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_100]),c_0_88])).

cnf(c_0_114,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_105])).

cnf(c_0_115,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(k2_wellord1(X1,X2),X3)),X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_85]),c_0_88])).

cnf(c_0_116,plain,
    ( k8_relat_1(X1,k2_wellord1(k6_relat_1(X1),X2)) = k2_wellord1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_107]),c_0_101])])).

cnf(c_0_117,plain,
    ( k7_relat_1(k2_wellord1(k6_relat_1(X1),X2),X1) = k2_wellord1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_108]),c_0_101])])).

cnf(c_0_118,negated_conjecture,
    ( r1_tarski(k3_relat_1(k2_wellord1(k6_relat_1(esk1_0),X1)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_85]),c_0_55])])).

cnf(c_0_119,negated_conjecture,
    ( k7_relat_1(X1,esk2_0) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),esk1_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_84])).

cnf(c_0_120,negated_conjecture,
    ( k8_relat_1(esk2_0,k6_relat_1(X1)) = k6_relat_1(X1)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_54]),c_0_55])])).

cnf(c_0_121,negated_conjecture,
    ( k8_relat_1(esk2_0,k2_wellord1(X1,esk1_0)) = k2_wellord1(k2_wellord1(X1,esk1_0),esk2_0)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_88])).

cnf(c_0_122,negated_conjecture,
    ( k8_relat_1(esk2_0,k2_wellord1(X1,esk1_0)) = k2_wellord1(X1,esk1_0)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_113]),c_0_88])).

cnf(c_0_123,plain,
    ( k2_wellord1(X1,k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))) = k2_wellord1(k2_wellord1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_89,c_0_114])).

cnf(c_0_124,plain,
    ( k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[c_0_105,c_0_114])).

cnf(c_0_125,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_105])).

cnf(c_0_126,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,k3_relat_1(k2_wellord1(k2_wellord1(X3,X2),X4))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_115])).

cnf(c_0_127,plain,
    ( k2_wellord1(k2_wellord1(k6_relat_1(X1),X2),X1) = k2_wellord1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_116]),c_0_117]),c_0_101])])).

cnf(c_0_128,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,k3_relat_1(k2_wellord1(k6_relat_1(esk1_0),X2))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_118])).

cnf(c_0_129,negated_conjecture,
    ( k7_relat_1(k6_relat_1(X1),esk2_0) = k6_relat_1(X1)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_57]),c_0_55])])).

cnf(c_0_130,negated_conjecture,
    ( k7_relat_1(k6_relat_1(X1),esk2_0) = k2_wellord1(k6_relat_1(X1),esk2_0)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_120]),c_0_55])])).

cnf(c_0_131,negated_conjecture,
    ( k2_wellord1(k2_wellord1(X1,esk1_0),esk2_0) = k2_wellord1(X1,esk1_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_132,plain,
    ( k2_wellord1(k2_wellord1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X2),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_123]),c_0_124]),c_0_124]),c_0_124]),c_0_125])])).

cnf(c_0_133,plain,
    ( k8_relat_1(X1,k6_relat_1(X2)) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_54]),c_0_55])])).

cnf(c_0_134,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_relat_1(k2_wellord1(k6_relat_1(X3),X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_55])])).

cnf(c_0_135,negated_conjecture,
    ( r1_tarski(k1_relat_1(k2_wellord1(k6_relat_1(esk1_0),X1)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_97]),c_0_101])])).

cnf(c_0_136,negated_conjecture,
    ( k2_wellord1(k6_relat_1(X1),esk2_0) = k6_relat_1(X1)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_129,c_0_130])).

cnf(c_0_137,negated_conjecture,
    ( k2_wellord1(k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)),esk1_0) = k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_132]),c_0_125])])).

cnf(c_0_138,plain,
    ( k3_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_86,c_0_124])).

cnf(c_0_139,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_87]),c_0_114])).

fof(c_0_140,plain,(
    ! [X52,X53] :
      ( ~ v1_relat_1(X53)
      | k7_relat_1(X53,X52) = k5_relat_1(k6_relat_1(X52),X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_141,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X1,k3_relat_1(k2_wellord1(X2,X3)))),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_106,c_0_71])).

cnf(c_0_142,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_57]),c_0_55])])).

cnf(c_0_143,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k2_wellord1(k6_relat_1(X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_133]),c_0_55])])).

cnf(c_0_144,plain,
    ( r1_tarski(k1_relat_1(k2_wellord1(k6_relat_1(X1),X2)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_97]),c_0_101])])).

cnf(c_0_145,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(k6_relat_1(X1),X2)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_100]),c_0_101])])).

cnf(c_0_146,negated_conjecture,
    ( k7_relat_1(k2_wellord1(k6_relat_1(esk1_0),X1),esk2_0) = k2_wellord1(k6_relat_1(esk1_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_135]),c_0_101])])).

cnf(c_0_147,negated_conjecture,
    ( k2_wellord1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),esk2_0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))
    | ~ r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),esk1_0) ),
    inference(spm,[status(thm)],[c_0_136,c_0_124])).

cnf(c_0_148,negated_conjecture,
    ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(esk1_0),k6_relat_1(esk2_0))),esk1_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_137]),c_0_138]),c_0_125])]),c_0_139])).

cnf(c_0_149,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_140])).

cnf(c_0_150,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X4)
    | ~ r1_tarski(X1,k3_relat_1(k2_wellord1(X4,k3_relat_1(k2_wellord1(X3,X2))))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_141])).

cnf(c_0_151,plain,
    ( k2_wellord1(k6_relat_1(X1),X2) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_142,c_0_143])).

cnf(c_0_152,plain,
    ( k7_relat_1(k2_wellord1(k6_relat_1(X1),X2),X2) = k2_wellord1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_144]),c_0_101])])).

cnf(c_0_153,plain,
    ( k8_relat_1(X1,k2_wellord1(k6_relat_1(X2),X1)) = k2_wellord1(k6_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_145]),c_0_101])])).

cnf(c_0_154,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k3_relat_1(k2_wellord1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_85])).

cnf(c_0_155,negated_conjecture,
    ( r1_tarski(k2_relat_1(k2_wellord1(k6_relat_1(esk1_0),X1)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_100]),c_0_101])])).

cnf(c_0_156,negated_conjecture,
    ( k8_relat_1(esk2_0,k2_wellord1(k6_relat_1(esk1_0),X1)) = k2_wellord1(k2_wellord1(k6_relat_1(esk1_0),X1),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_146]),c_0_101])])).

cnf(c_0_157,negated_conjecture,
    ( k2_wellord1(k5_relat_1(k6_relat_1(esk1_0),k6_relat_1(esk2_0)),esk2_0) = k5_relat_1(k6_relat_1(esk1_0),k6_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_147,c_0_148])).

cnf(c_0_158,plain,
    ( k7_relat_1(k2_wellord1(X1,X2),X2) = k2_wellord1(k7_relat_1(X1,X2),X2)
    | ~ v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_111])).

cnf(c_0_159,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_149]),c_0_55])])).

cnf(c_0_160,negated_conjecture,
    ( k7_relat_1(k2_wellord1(X1,esk1_0),esk2_0) = k2_wellord1(k2_wellord1(X1,esk1_0),esk2_0)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_122]),c_0_88])).

cnf(c_0_161,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,k3_relat_1(k2_wellord1(X3,X4)))
    | ~ r1_tarski(X4,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_151]),c_0_55]),c_0_86])])).

cnf(c_0_162,plain,
    ( k2_wellord1(k2_wellord1(k6_relat_1(X1),X2),X2) = k2_wellord1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_152]),c_0_153]),c_0_101])])).

cnf(c_0_163,plain,
    ( r1_tarski(k1_relat_1(k2_wellord1(X1,X2)),k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_154,c_0_97]),c_0_88])).

cnf(c_0_164,negated_conjecture,
    ( k2_wellord1(k2_wellord1(k6_relat_1(esk1_0),X1),esk2_0) = k2_wellord1(k6_relat_1(esk1_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_155]),c_0_156]),c_0_101])])).

cnf(c_0_165,negated_conjecture,
    ( k2_wellord1(k5_relat_1(k6_relat_1(esk1_0),k6_relat_1(esk2_0)),esk1_0) = k5_relat_1(k6_relat_1(esk1_0),k6_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_132,c_0_157])).

cnf(c_0_166,plain,
    ( k2_wellord1(k7_relat_1(k6_relat_1(X1),X2),X2) = k2_wellord1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158,c_0_152]),c_0_159]),c_0_55])])).

cnf(c_0_167,negated_conjecture,
    ( k7_relat_1(k6_relat_1(esk1_0),esk2_0) = k6_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_72]),c_0_55])])).

cnf(c_0_168,negated_conjecture,
    ( k2_wellord1(k2_wellord1(k6_relat_1(esk2_0),esk1_0),esk2_0) = k2_wellord1(k6_relat_1(esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_117]),c_0_55])])).

cnf(c_0_169,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_relat_1(k2_wellord1(k6_relat_1(X3),X4)))
    | ~ r1_tarski(X4,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161,c_0_162]),c_0_101])])).

cnf(c_0_170,negated_conjecture,
    ( r1_tarski(k1_relat_1(k2_wellord1(k6_relat_1(esk1_0),X1)),k3_relat_1(k2_wellord1(k6_relat_1(esk1_0),X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163,c_0_164]),c_0_101])])).

cnf(c_0_171,plain,
    ( k2_wellord1(X1,k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k2_wellord1(k2_wellord1(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_149]),c_0_55])])).

cnf(c_0_172,negated_conjecture,
    ( k7_relat_1(k6_relat_1(esk2_0),esk1_0) = k2_wellord1(k6_relat_1(esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_149]),c_0_166]),c_0_55])])).

cnf(c_0_173,negated_conjecture,
    ( k8_relat_1(esk2_0,k6_relat_1(esk1_0)) = k2_wellord1(k6_relat_1(esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_167]),c_0_55])])).

cnf(c_0_174,negated_conjecture,
    ( r1_tarski(X1,esk1_0)
    | ~ r1_tarski(X1,k3_relat_1(k2_wellord1(k6_relat_1(esk2_0),esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_168]),c_0_55])])).

cnf(c_0_175,negated_conjecture,
    ( r1_tarski(k1_relat_1(k2_wellord1(k6_relat_1(esk1_0),X1)),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_169,c_0_170])).

cnf(c_0_176,negated_conjecture,
    ( k2_wellord1(X1,k1_relat_1(k2_wellord1(k6_relat_1(esk2_0),esk1_0))) = k2_wellord1(k2_wellord1(X1,esk2_0),esk1_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_171,c_0_172])).

cnf(c_0_177,negated_conjecture,
    ( k2_wellord1(k6_relat_1(esk1_0),esk2_0) = k6_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_173]),c_0_77])])).

cnf(c_0_178,negated_conjecture,
    ( r1_tarski(k1_relat_1(k2_wellord1(k6_relat_1(esk2_0),esk1_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174,c_0_97]),c_0_101])])).

cnf(c_0_179,negated_conjecture,
    ( r1_tarski(esk1_0,X1)
    | ~ r1_tarski(k1_relat_1(k2_wellord1(k6_relat_1(esk2_0),esk1_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_175,c_0_176]),c_0_177]),c_0_72]),c_0_57]),c_0_55])])).

cnf(c_0_180,negated_conjecture,
    ( k1_relat_1(k2_wellord1(k6_relat_1(esk2_0),esk1_0)) = esk1_0
    | ~ r1_tarski(esk1_0,k1_relat_1(k2_wellord1(k6_relat_1(esk2_0),esk1_0))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_178])).

cnf(c_0_181,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(k2_wellord1(k6_relat_1(esk2_0),esk1_0))) ),
    inference(spm,[status(thm)],[c_0_179,c_0_40])).

cnf(c_0_182,negated_conjecture,
    ( k1_relat_1(k2_wellord1(k6_relat_1(esk2_0),esk1_0)) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_180,c_0_181])])).

cnf(c_0_183,negated_conjecture,
    ( k2_wellord1(k2_wellord1(esk3_0,esk2_0),esk1_0) != k2_wellord1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_184,negated_conjecture,
    ( k2_wellord1(k2_wellord1(X1,esk2_0),esk1_0) = k2_wellord1(X1,esk1_0)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_176,c_0_182])).

cnf(c_0_185,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_186,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_183,c_0_184]),c_0_185])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.81/2.00  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.81/2.00  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.81/2.00  #
% 1.81/2.00  # Preprocessing time       : 0.028 s
% 1.81/2.00  # Presaturation interreduction done
% 1.81/2.00  
% 1.81/2.00  # Proof found!
% 1.81/2.00  # SZS status Theorem
% 1.81/2.00  # SZS output start CNFRefutation
% 1.81/2.00  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.81/2.00  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.81/2.00  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.81/2.00  fof(t125_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k8_relat_1(X1,X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 1.81/2.00  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.81/2.00  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.81/2.00  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 1.81/2.00  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 1.81/2.00  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 1.81/2.00  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 1.81/2.00  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.81/2.00  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.81/2.00  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 1.81/2.00  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 1.81/2.00  fof(t17_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_wellord1(X2,X1)=k7_relat_1(k8_relat_1(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_wellord1)).
% 1.81/2.00  fof(t29_wellord1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k2_wellord1(k2_wellord1(X3,X2),X1)=k2_wellord1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_wellord1)).
% 1.81/2.00  fof(t20_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),k3_relat_1(X2))&r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_wellord1)).
% 1.81/2.00  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.81/2.00  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.81/2.00  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.81/2.00  fof(t26_wellord1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k2_wellord1(k2_wellord1(X3,X1),X2)=k2_wellord1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_wellord1)).
% 1.81/2.00  fof(dt_k2_wellord1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k2_wellord1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_wellord1)).
% 1.81/2.00  fof(t43_funct_1, axiom, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 1.81/2.00  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 1.81/2.00  fof(t18_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_wellord1(X2,X1)=k8_relat_1(X1,k7_relat_1(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_wellord1)).
% 1.81/2.00  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 1.81/2.00  fof(c_0_26, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.81/2.00  fof(c_0_27, plain, ![X44, X45]:k3_tarski(k2_tarski(X44,X45))=k2_xboole_0(X44,X45), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 1.81/2.00  fof(c_0_28, plain, ![X17, X18]:k1_enumset1(X17,X17,X18)=k2_tarski(X17,X18), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.81/2.00  fof(c_0_29, plain, ![X49, X50]:(~v1_relat_1(X50)|(~r1_tarski(k2_relat_1(X50),X49)|k8_relat_1(X49,X50)=X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).
% 1.81/2.00  cnf(c_0_30, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.81/2.00  fof(c_0_31, plain, ![X13, X14]:r1_tarski(X13,k2_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 1.81/2.00  cnf(c_0_32, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.81/2.00  cnf(c_0_33, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.81/2.00  fof(c_0_34, plain, ![X19, X20, X21]:k2_enumset1(X19,X19,X20,X21)=k1_enumset1(X19,X20,X21), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.81/2.00  fof(c_0_35, plain, ![X22, X23, X24, X25]:k3_enumset1(X22,X22,X23,X24,X25)=k2_enumset1(X22,X23,X24,X25), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 1.81/2.00  fof(c_0_36, plain, ![X26, X27, X28, X29, X30]:k4_enumset1(X26,X26,X27,X28,X29,X30)=k3_enumset1(X26,X27,X28,X29,X30), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 1.81/2.00  fof(c_0_37, plain, ![X31, X32, X33, X34, X35, X36]:k5_enumset1(X31,X31,X32,X33,X34,X35,X36)=k4_enumset1(X31,X32,X33,X34,X35,X36), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 1.81/2.00  fof(c_0_38, plain, ![X37, X38, X39, X40, X41, X42, X43]:k6_enumset1(X37,X37,X38,X39,X40,X41,X42,X43)=k5_enumset1(X37,X38,X39,X40,X41,X42,X43), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 1.81/2.00  cnf(c_0_39, plain, (k8_relat_1(X2,X1)=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.81/2.00  cnf(c_0_40, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_30])).
% 1.81/2.00  fof(c_0_41, plain, ![X51]:(k1_relat_1(k6_relat_1(X51))=X51&k2_relat_1(k6_relat_1(X51))=X51), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 1.81/2.00  fof(c_0_42, plain, ![X57]:(v1_relat_1(k6_relat_1(X57))&v1_funct_1(k6_relat_1(X57))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 1.81/2.00  fof(c_0_43, plain, ![X56]:(~v1_relat_1(X56)|k7_relat_1(X56,k1_relat_1(X56))=X56), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 1.81/2.00  cnf(c_0_44, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.81/2.00  cnf(c_0_45, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 1.81/2.00  cnf(c_0_46, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.81/2.00  cnf(c_0_47, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.81/2.00  cnf(c_0_48, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.81/2.00  cnf(c_0_49, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 1.81/2.00  cnf(c_0_50, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 1.81/2.00  fof(c_0_51, plain, ![X48]:(~v1_relat_1(X48)|k3_relat_1(X48)=k2_xboole_0(k1_relat_1(X48),k2_relat_1(X48))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 1.81/2.00  fof(c_0_52, plain, ![X62, X63]:(~v1_relat_1(X63)|k2_wellord1(X63,X62)=k7_relat_1(k8_relat_1(X62,X63),X62)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_wellord1])])).
% 1.81/2.00  cnf(c_0_53, plain, (k8_relat_1(k2_relat_1(X1),X1)=X1|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 1.81/2.00  cnf(c_0_54, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.81/2.00  cnf(c_0_55, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.81/2.00  cnf(c_0_56, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.81/2.00  cnf(c_0_57, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.81/2.00  fof(c_0_58, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k2_wellord1(k2_wellord1(X3,X2),X1)=k2_wellord1(X3,X1)))), inference(assume_negation,[status(cth)],[t29_wellord1])).
% 1.81/2.00  cnf(c_0_59, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.81/2.00  cnf(c_0_60, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50])).
% 1.81/2.00  cnf(c_0_61, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 1.81/2.00  fof(c_0_62, plain, ![X66, X67]:((r1_tarski(k3_relat_1(k2_wellord1(X67,X66)),k3_relat_1(X67))|~v1_relat_1(X67))&(r1_tarski(k3_relat_1(k2_wellord1(X67,X66)),X66)|~v1_relat_1(X67))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_wellord1])])])).
% 1.81/2.00  cnf(c_0_63, plain, (k2_wellord1(X1,X2)=k7_relat_1(k8_relat_1(X2,X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 1.81/2.00  cnf(c_0_64, plain, (k8_relat_1(X1,k6_relat_1(X1))=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])])).
% 1.81/2.00  cnf(c_0_65, plain, (k7_relat_1(k6_relat_1(X1),X1)=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_55])])).
% 1.81/2.00  fof(c_0_66, plain, ![X46, X47]:k1_setfam_1(k2_tarski(X46,X47))=k3_xboole_0(X46,X47), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 1.81/2.00  fof(c_0_67, plain, ![X10, X11, X12]:(~r1_tarski(X10,X11)|~r1_tarski(X11,X12)|r1_tarski(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 1.81/2.00  fof(c_0_68, negated_conjecture, (v1_relat_1(esk3_0)&(r1_tarski(esk1_0,esk2_0)&k2_wellord1(k2_wellord1(esk3_0,esk2_0),esk1_0)!=k2_wellord1(esk3_0,esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_58])])])).
% 1.81/2.00  cnf(c_0_69, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=X1|~r1_tarski(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X1)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 1.81/2.00  cnf(c_0_70, plain, (k3_relat_1(X1)=k3_tarski(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_45]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50])).
% 1.81/2.00  cnf(c_0_71, plain, (r1_tarski(k3_relat_1(k2_wellord1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 1.81/2.00  cnf(c_0_72, plain, (k2_wellord1(k6_relat_1(X1),X1)=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), c_0_55])])).
% 1.81/2.00  fof(c_0_73, plain, ![X15, X16]:k2_tarski(X15,X16)=k2_tarski(X16,X15), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 1.81/2.00  fof(c_0_74, plain, ![X68, X69, X70]:(~v1_relat_1(X70)|k2_wellord1(k2_wellord1(X70,X68),X69)=k2_wellord1(X70,k3_xboole_0(X68,X69))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_wellord1])])).
% 1.81/2.00  cnf(c_0_75, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 1.81/2.00  cnf(c_0_76, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 1.81/2.00  cnf(c_0_77, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 1.81/2.00  cnf(c_0_78, plain, (k3_relat_1(X1)=k1_relat_1(X1)|~v1_relat_1(X1)|~r1_tarski(k3_relat_1(X1),k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 1.81/2.00  cnf(c_0_79, plain, (r1_tarski(k3_relat_1(k6_relat_1(X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_55])])).
% 1.81/2.00  cnf(c_0_80, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 1.81/2.00  fof(c_0_81, plain, ![X60, X61]:(~v1_relat_1(X60)|v1_relat_1(k2_wellord1(X60,X61))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).
% 1.81/2.00  cnf(c_0_82, plain, (k2_wellord1(k2_wellord1(X1,X2),X3)=k2_wellord1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 1.81/2.00  cnf(c_0_83, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_75, c_0_33])).
% 1.81/2.00  cnf(c_0_84, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 1.81/2.00  cnf(c_0_85, plain, (r1_tarski(k3_relat_1(k2_wellord1(X1,X2)),k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 1.81/2.00  cnf(c_0_86, plain, (k3_relat_1(k6_relat_1(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_57]), c_0_55]), c_0_79])])).
% 1.81/2.00  cnf(c_0_87, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_33]), c_0_33]), c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_50]), c_0_50])).
% 1.81/2.00  cnf(c_0_88, plain, (v1_relat_1(k2_wellord1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 1.81/2.00  cnf(c_0_89, plain, (k2_wellord1(k2_wellord1(X1,X2),X3)=k2_wellord1(X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_83]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50])).
% 1.81/2.00  cnf(c_0_90, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X2,esk1_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_76, c_0_84])).
% 1.81/2.00  fof(c_0_91, plain, ![X58, X59]:k5_relat_1(k6_relat_1(X59),k6_relat_1(X58))=k6_relat_1(k3_xboole_0(X58,X59)), inference(variable_rename,[status(thm)],[t43_funct_1])).
% 1.81/2.00  cnf(c_0_92, plain, (r1_tarski(k3_relat_1(k2_wellord1(k6_relat_1(X1),X2)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_55])])).
% 1.81/2.00  cnf(c_0_93, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))), inference(spm,[status(thm)],[c_0_60, c_0_87])).
% 1.81/2.00  cnf(c_0_94, plain, (v1_relat_1(k2_wellord1(k2_wellord1(X1,X2),X3))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 1.81/2.00  fof(c_0_95, plain, ![X54, X55]:(~v1_relat_1(X55)|(~r1_tarski(k1_relat_1(X55),X54)|k7_relat_1(X55,X54)=X55)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 1.81/2.00  cnf(c_0_96, negated_conjecture, (r1_tarski(X1,esk2_0)|~v1_relat_1(X2)|~r1_tarski(X1,k3_relat_1(k2_wellord1(X2,esk1_0)))), inference(spm,[status(thm)],[c_0_90, c_0_71])).
% 1.81/2.00  cnf(c_0_97, plain, (r1_tarski(k1_relat_1(X1),k3_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_60, c_0_70])).
% 1.81/2.00  cnf(c_0_98, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k3_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_91])).
% 1.81/2.00  cnf(c_0_99, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_relat_1(k2_wellord1(k6_relat_1(X2),X3)))), inference(spm,[status(thm)],[c_0_76, c_0_92])).
% 1.81/2.00  cnf(c_0_100, plain, (r1_tarski(k2_relat_1(X1),k3_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_93, c_0_70])).
% 1.81/2.00  cnf(c_0_101, plain, (v1_relat_1(k2_wellord1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_72]), c_0_55])])).
% 1.81/2.00  fof(c_0_102, plain, ![X64, X65]:(~v1_relat_1(X65)|k2_wellord1(X65,X64)=k8_relat_1(X64,k7_relat_1(X65,X64))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_wellord1])])).
% 1.81/2.00  cnf(c_0_103, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_95])).
% 1.81/2.00  cnf(c_0_104, negated_conjecture, (r1_tarski(k1_relat_1(k2_wellord1(X1,esk1_0)),esk2_0)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_88])).
% 1.81/2.00  cnf(c_0_105, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98, c_0_83]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50])).
% 1.81/2.00  cnf(c_0_106, plain, (r1_tarski(X1,X2)|~v1_relat_1(X3)|~r1_tarski(X1,k3_relat_1(k2_wellord1(X3,X2)))), inference(spm,[status(thm)],[c_0_76, c_0_71])).
% 1.81/2.00  cnf(c_0_107, plain, (r1_tarski(k2_relat_1(k2_wellord1(k6_relat_1(X1),X2)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_101])])).
% 1.81/2.00  cnf(c_0_108, plain, (r1_tarski(k1_relat_1(k2_wellord1(k6_relat_1(X1),X2)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_97]), c_0_101])])).
% 1.81/2.00  cnf(c_0_109, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,k3_relat_1(k6_relat_1(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_72]), c_0_55])])).
% 1.81/2.00  cnf(c_0_110, negated_conjecture, (k8_relat_1(esk2_0,X1)=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),esk1_0)), inference(spm,[status(thm)],[c_0_39, c_0_84])).
% 1.81/2.00  cnf(c_0_111, plain, (k2_wellord1(X1,X2)=k8_relat_1(X2,k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 1.81/2.00  cnf(c_0_112, negated_conjecture, (k7_relat_1(k2_wellord1(X1,esk1_0),esk2_0)=k2_wellord1(X1,esk1_0)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_88])).
% 1.81/2.00  cnf(c_0_113, negated_conjecture, (r1_tarski(k2_relat_1(k2_wellord1(X1,esk1_0)),esk2_0)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_100]), c_0_88])).
% 1.81/2.00  cnf(c_0_114, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))), inference(spm,[status(thm)],[c_0_57, c_0_105])).
% 1.81/2.00  cnf(c_0_115, plain, (r1_tarski(k3_relat_1(k2_wellord1(k2_wellord1(X1,X2),X3)),X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_85]), c_0_88])).
% 1.81/2.00  cnf(c_0_116, plain, (k8_relat_1(X1,k2_wellord1(k6_relat_1(X1),X2))=k2_wellord1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_107]), c_0_101])])).
% 1.81/2.00  cnf(c_0_117, plain, (k7_relat_1(k2_wellord1(k6_relat_1(X1),X2),X1)=k2_wellord1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_108]), c_0_101])])).
% 1.81/2.00  cnf(c_0_118, negated_conjecture, (r1_tarski(k3_relat_1(k2_wellord1(k6_relat_1(esk1_0),X1)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_85]), c_0_55])])).
% 1.81/2.00  cnf(c_0_119, negated_conjecture, (k7_relat_1(X1,esk2_0)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),esk1_0)), inference(spm,[status(thm)],[c_0_103, c_0_84])).
% 1.81/2.00  cnf(c_0_120, negated_conjecture, (k8_relat_1(esk2_0,k6_relat_1(X1))=k6_relat_1(X1)|~r1_tarski(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_54]), c_0_55])])).
% 1.81/2.00  cnf(c_0_121, negated_conjecture, (k8_relat_1(esk2_0,k2_wellord1(X1,esk1_0))=k2_wellord1(k2_wellord1(X1,esk1_0),esk2_0)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_88])).
% 1.81/2.00  cnf(c_0_122, negated_conjecture, (k8_relat_1(esk2_0,k2_wellord1(X1,esk1_0))=k2_wellord1(X1,esk1_0)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_113]), c_0_88])).
% 1.81/2.00  cnf(c_0_123, plain, (k2_wellord1(X1,k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))))=k2_wellord1(k2_wellord1(X1,X3),X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_89, c_0_114])).
% 1.81/2.00  cnf(c_0_124, plain, (k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(rw,[status(thm)],[c_0_105, c_0_114])).
% 1.81/2.00  cnf(c_0_125, plain, (v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))), inference(spm,[status(thm)],[c_0_55, c_0_105])).
% 1.81/2.00  cnf(c_0_126, plain, (r1_tarski(X1,X2)|~v1_relat_1(X3)|~r1_tarski(X1,k3_relat_1(k2_wellord1(k2_wellord1(X3,X2),X4)))), inference(spm,[status(thm)],[c_0_76, c_0_115])).
% 1.81/2.00  cnf(c_0_127, plain, (k2_wellord1(k2_wellord1(k6_relat_1(X1),X2),X1)=k2_wellord1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_116]), c_0_117]), c_0_101])])).
% 1.81/2.00  cnf(c_0_128, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,k3_relat_1(k2_wellord1(k6_relat_1(esk1_0),X2)))), inference(spm,[status(thm)],[c_0_76, c_0_118])).
% 1.81/2.00  cnf(c_0_129, negated_conjecture, (k7_relat_1(k6_relat_1(X1),esk2_0)=k6_relat_1(X1)|~r1_tarski(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_57]), c_0_55])])).
% 1.81/2.00  cnf(c_0_130, negated_conjecture, (k7_relat_1(k6_relat_1(X1),esk2_0)=k2_wellord1(k6_relat_1(X1),esk2_0)|~r1_tarski(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_120]), c_0_55])])).
% 1.81/2.00  cnf(c_0_131, negated_conjecture, (k2_wellord1(k2_wellord1(X1,esk1_0),esk2_0)=k2_wellord1(X1,esk1_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_121, c_0_122])).
% 1.81/2.00  cnf(c_0_132, plain, (k2_wellord1(k2_wellord1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X2),X1)=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_123]), c_0_124]), c_0_124]), c_0_124]), c_0_125])])).
% 1.81/2.00  cnf(c_0_133, plain, (k8_relat_1(X1,k6_relat_1(X2))=k6_relat_1(X2)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_54]), c_0_55])])).
% 1.81/2.00  cnf(c_0_134, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_relat_1(k2_wellord1(k6_relat_1(X3),X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_127]), c_0_55])])).
% 1.81/2.00  cnf(c_0_135, negated_conjecture, (r1_tarski(k1_relat_1(k2_wellord1(k6_relat_1(esk1_0),X1)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_97]), c_0_101])])).
% 1.81/2.00  cnf(c_0_136, negated_conjecture, (k2_wellord1(k6_relat_1(X1),esk2_0)=k6_relat_1(X1)|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_129, c_0_130])).
% 1.81/2.00  cnf(c_0_137, negated_conjecture, (k2_wellord1(k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)),esk1_0)=k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_132]), c_0_125])])).
% 1.81/2.00  cnf(c_0_138, plain, (k3_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))), inference(spm,[status(thm)],[c_0_86, c_0_124])).
% 1.81/2.00  cnf(c_0_139, plain, (k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_87]), c_0_114])).
% 1.81/2.00  fof(c_0_140, plain, ![X52, X53]:(~v1_relat_1(X53)|k7_relat_1(X53,X52)=k5_relat_1(k6_relat_1(X52),X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 1.81/2.00  cnf(c_0_141, plain, (r1_tarski(k3_relat_1(k2_wellord1(X1,k3_relat_1(k2_wellord1(X2,X3)))),X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_106, c_0_71])).
% 1.81/2.00  cnf(c_0_142, plain, (k7_relat_1(k6_relat_1(X1),X2)=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_57]), c_0_55])])).
% 1.81/2.00  cnf(c_0_143, plain, (k7_relat_1(k6_relat_1(X1),X2)=k2_wellord1(k6_relat_1(X1),X2)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_133]), c_0_55])])).
% 1.81/2.00  cnf(c_0_144, plain, (r1_tarski(k1_relat_1(k2_wellord1(k6_relat_1(X1),X2)),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_97]), c_0_101])])).
% 1.81/2.00  cnf(c_0_145, plain, (r1_tarski(k2_relat_1(k2_wellord1(k6_relat_1(X1),X2)),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_100]), c_0_101])])).
% 1.81/2.00  cnf(c_0_146, negated_conjecture, (k7_relat_1(k2_wellord1(k6_relat_1(esk1_0),X1),esk2_0)=k2_wellord1(k6_relat_1(esk1_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_135]), c_0_101])])).
% 1.81/2.00  cnf(c_0_147, negated_conjecture, (k2_wellord1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),esk2_0)=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))|~r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),esk1_0)), inference(spm,[status(thm)],[c_0_136, c_0_124])).
% 1.81/2.00  cnf(c_0_148, negated_conjecture, (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(esk1_0),k6_relat_1(esk2_0))),esk1_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_137]), c_0_138]), c_0_125])]), c_0_139])).
% 1.81/2.00  cnf(c_0_149, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_140])).
% 1.81/2.00  cnf(c_0_150, plain, (r1_tarski(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X4)|~r1_tarski(X1,k3_relat_1(k2_wellord1(X4,k3_relat_1(k2_wellord1(X3,X2)))))), inference(spm,[status(thm)],[c_0_76, c_0_141])).
% 1.81/2.00  cnf(c_0_151, plain, (k2_wellord1(k6_relat_1(X1),X2)=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_142, c_0_143])).
% 1.81/2.00  cnf(c_0_152, plain, (k7_relat_1(k2_wellord1(k6_relat_1(X1),X2),X2)=k2_wellord1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_144]), c_0_101])])).
% 1.81/2.00  cnf(c_0_153, plain, (k8_relat_1(X1,k2_wellord1(k6_relat_1(X2),X1))=k2_wellord1(k6_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_145]), c_0_101])])).
% 1.81/2.00  cnf(c_0_154, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,k3_relat_1(k2_wellord1(X2,X3)))), inference(spm,[status(thm)],[c_0_76, c_0_85])).
% 1.81/2.00  cnf(c_0_155, negated_conjecture, (r1_tarski(k2_relat_1(k2_wellord1(k6_relat_1(esk1_0),X1)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_100]), c_0_101])])).
% 1.81/2.00  cnf(c_0_156, negated_conjecture, (k8_relat_1(esk2_0,k2_wellord1(k6_relat_1(esk1_0),X1))=k2_wellord1(k2_wellord1(k6_relat_1(esk1_0),X1),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_146]), c_0_101])])).
% 1.81/2.00  cnf(c_0_157, negated_conjecture, (k2_wellord1(k5_relat_1(k6_relat_1(esk1_0),k6_relat_1(esk2_0)),esk2_0)=k5_relat_1(k6_relat_1(esk1_0),k6_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_147, c_0_148])).
% 1.81/2.00  cnf(c_0_158, plain, (k7_relat_1(k2_wellord1(X1,X2),X2)=k2_wellord1(k7_relat_1(X1,X2),X2)|~v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_63, c_0_111])).
% 1.81/2.00  cnf(c_0_159, plain, (v1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_149]), c_0_55])])).
% 1.81/2.00  cnf(c_0_160, negated_conjecture, (k7_relat_1(k2_wellord1(X1,esk1_0),esk2_0)=k2_wellord1(k2_wellord1(X1,esk1_0),esk2_0)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_122]), c_0_88])).
% 1.81/2.00  cnf(c_0_161, plain, (r1_tarski(X1,X2)|~v1_relat_1(X3)|~r1_tarski(X1,k3_relat_1(k2_wellord1(X3,X4)))|~r1_tarski(X4,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150, c_0_151]), c_0_55]), c_0_86])])).
% 1.81/2.00  cnf(c_0_162, plain, (k2_wellord1(k2_wellord1(k6_relat_1(X1),X2),X2)=k2_wellord1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_152]), c_0_153]), c_0_101])])).
% 1.81/2.00  cnf(c_0_163, plain, (r1_tarski(k1_relat_1(k2_wellord1(X1,X2)),k3_relat_1(X1))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_154, c_0_97]), c_0_88])).
% 1.81/2.00  cnf(c_0_164, negated_conjecture, (k2_wellord1(k2_wellord1(k6_relat_1(esk1_0),X1),esk2_0)=k2_wellord1(k6_relat_1(esk1_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_155]), c_0_156]), c_0_101])])).
% 1.81/2.00  cnf(c_0_165, negated_conjecture, (k2_wellord1(k5_relat_1(k6_relat_1(esk1_0),k6_relat_1(esk2_0)),esk1_0)=k5_relat_1(k6_relat_1(esk1_0),k6_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_132, c_0_157])).
% 1.81/2.00  cnf(c_0_166, plain, (k2_wellord1(k7_relat_1(k6_relat_1(X1),X2),X2)=k2_wellord1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158, c_0_152]), c_0_159]), c_0_55])])).
% 1.81/2.00  cnf(c_0_167, negated_conjecture, (k7_relat_1(k6_relat_1(esk1_0),esk2_0)=k6_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_72]), c_0_55])])).
% 1.81/2.00  cnf(c_0_168, negated_conjecture, (k2_wellord1(k2_wellord1(k6_relat_1(esk2_0),esk1_0),esk2_0)=k2_wellord1(k6_relat_1(esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160, c_0_117]), c_0_55])])).
% 1.81/2.00  cnf(c_0_169, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_relat_1(k2_wellord1(k6_relat_1(X3),X4)))|~r1_tarski(X4,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161, c_0_162]), c_0_101])])).
% 1.81/2.00  cnf(c_0_170, negated_conjecture, (r1_tarski(k1_relat_1(k2_wellord1(k6_relat_1(esk1_0),X1)),k3_relat_1(k2_wellord1(k6_relat_1(esk1_0),X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163, c_0_164]), c_0_101])])).
% 1.81/2.00  cnf(c_0_171, plain, (k2_wellord1(X1,k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)))=k2_wellord1(k2_wellord1(X1,X2),X3)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_149]), c_0_55])])).
% 1.81/2.00  cnf(c_0_172, negated_conjecture, (k7_relat_1(k6_relat_1(esk2_0),esk1_0)=k2_wellord1(k6_relat_1(esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165, c_0_149]), c_0_166]), c_0_55])])).
% 1.81/2.00  cnf(c_0_173, negated_conjecture, (k8_relat_1(esk2_0,k6_relat_1(esk1_0))=k2_wellord1(k6_relat_1(esk1_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_167]), c_0_55])])).
% 1.81/2.00  cnf(c_0_174, negated_conjecture, (r1_tarski(X1,esk1_0)|~r1_tarski(X1,k3_relat_1(k2_wellord1(k6_relat_1(esk2_0),esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_168]), c_0_55])])).
% 1.81/2.00  cnf(c_0_175, negated_conjecture, (r1_tarski(k1_relat_1(k2_wellord1(k6_relat_1(esk1_0),X1)),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_169, c_0_170])).
% 1.81/2.00  cnf(c_0_176, negated_conjecture, (k2_wellord1(X1,k1_relat_1(k2_wellord1(k6_relat_1(esk2_0),esk1_0)))=k2_wellord1(k2_wellord1(X1,esk2_0),esk1_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_171, c_0_172])).
% 1.81/2.00  cnf(c_0_177, negated_conjecture, (k2_wellord1(k6_relat_1(esk1_0),esk2_0)=k6_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_173]), c_0_77])])).
% 1.81/2.00  cnf(c_0_178, negated_conjecture, (r1_tarski(k1_relat_1(k2_wellord1(k6_relat_1(esk2_0),esk1_0)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174, c_0_97]), c_0_101])])).
% 1.81/2.00  cnf(c_0_179, negated_conjecture, (r1_tarski(esk1_0,X1)|~r1_tarski(k1_relat_1(k2_wellord1(k6_relat_1(esk2_0),esk1_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_175, c_0_176]), c_0_177]), c_0_72]), c_0_57]), c_0_55])])).
% 1.81/2.00  cnf(c_0_180, negated_conjecture, (k1_relat_1(k2_wellord1(k6_relat_1(esk2_0),esk1_0))=esk1_0|~r1_tarski(esk1_0,k1_relat_1(k2_wellord1(k6_relat_1(esk2_0),esk1_0)))), inference(spm,[status(thm)],[c_0_59, c_0_178])).
% 1.81/2.00  cnf(c_0_181, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(k2_wellord1(k6_relat_1(esk2_0),esk1_0)))), inference(spm,[status(thm)],[c_0_179, c_0_40])).
% 1.81/2.00  cnf(c_0_182, negated_conjecture, (k1_relat_1(k2_wellord1(k6_relat_1(esk2_0),esk1_0))=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_180, c_0_181])])).
% 1.81/2.00  cnf(c_0_183, negated_conjecture, (k2_wellord1(k2_wellord1(esk3_0,esk2_0),esk1_0)!=k2_wellord1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 1.81/2.00  cnf(c_0_184, negated_conjecture, (k2_wellord1(k2_wellord1(X1,esk2_0),esk1_0)=k2_wellord1(X1,esk1_0)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_176, c_0_182])).
% 1.81/2.00  cnf(c_0_185, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 1.81/2.00  cnf(c_0_186, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_183, c_0_184]), c_0_185])]), ['proof']).
% 1.81/2.00  # SZS output end CNFRefutation
% 1.81/2.00  # Proof object total steps             : 187
% 1.81/2.00  # Proof object clause steps            : 134
% 1.81/2.00  # Proof object formula steps           : 53
% 1.81/2.00  # Proof object conjectures             : 51
% 1.81/2.00  # Proof object clause conjectures      : 48
% 1.81/2.00  # Proof object formula conjectures     : 3
% 1.81/2.00  # Proof object initial clauses used    : 31
% 1.81/2.00  # Proof object initial formulas used   : 26
% 1.81/2.00  # Proof object generating inferences   : 91
% 1.81/2.00  # Proof object simplifying inferences  : 167
% 1.81/2.00  # Training examples: 0 positive, 0 negative
% 1.81/2.00  # Parsed axioms                        : 26
% 1.81/2.00  # Removed by relevancy pruning/SinE    : 0
% 1.81/2.00  # Initial clauses                      : 33
% 1.81/2.00  # Removed in clause preprocessing      : 8
% 1.81/2.00  # Initial clauses in saturation        : 25
% 1.81/2.00  # Processed clauses                    : 11820
% 1.81/2.00  # ...of these trivial                  : 238
% 1.81/2.00  # ...subsumed                          : 9885
% 1.81/2.00  # ...remaining for further processing  : 1697
% 1.81/2.00  # Other redundant clauses eliminated   : 2
% 1.81/2.00  # Clauses deleted for lack of memory   : 0
% 1.81/2.00  # Backward-subsumed                    : 75
% 1.81/2.00  # Backward-rewritten                   : 140
% 1.81/2.00  # Generated clauses                    : 183291
% 1.81/2.00  # ...of the previous two non-trivial   : 167127
% 1.81/2.00  # Contextual simplify-reflections      : 111
% 1.81/2.00  # Paramodulations                      : 183289
% 1.81/2.00  # Factorizations                       : 0
% 1.81/2.00  # Equation resolutions                 : 2
% 1.81/2.00  # Propositional unsat checks           : 0
% 1.81/2.00  #    Propositional check models        : 0
% 1.81/2.00  #    Propositional check unsatisfiable : 0
% 1.81/2.00  #    Propositional clauses             : 0
% 1.81/2.00  #    Propositional clauses after purity: 0
% 1.81/2.00  #    Propositional unsat core size     : 0
% 1.81/2.00  #    Propositional preprocessing time  : 0.000
% 1.81/2.00  #    Propositional encoding time       : 0.000
% 1.81/2.00  #    Propositional solver time         : 0.000
% 1.81/2.00  #    Success case prop preproc time    : 0.000
% 1.81/2.00  #    Success case prop encoding time   : 0.000
% 1.81/2.00  #    Success case prop solver time     : 0.000
% 1.81/2.00  # Current number of processed clauses  : 1456
% 1.81/2.00  #    Positive orientable unit clauses  : 254
% 1.81/2.00  #    Positive unorientable unit clauses: 2
% 1.81/2.00  #    Negative unit clauses             : 1
% 1.81/2.00  #    Non-unit-clauses                  : 1199
% 1.81/2.00  # Current number of unprocessed clauses: 154005
% 1.81/2.00  # ...number of literals in the above   : 449214
% 1.81/2.00  # Current number of archived formulas  : 0
% 1.81/2.00  # Current number of archived clauses   : 247
% 1.81/2.00  # Clause-clause subsumption calls (NU) : 319079
% 1.81/2.00  # Rec. Clause-clause subsumption calls : 215680
% 1.81/2.00  # Non-unit clause-clause subsumptions  : 10070
% 1.81/2.00  # Unit Clause-clause subsumption calls : 2480
% 1.81/2.00  # Rewrite failures with RHS unbound    : 0
% 1.81/2.00  # BW rewrite match attempts            : 7464
% 1.81/2.00  # BW rewrite match successes           : 69
% 1.81/2.00  # Condensation attempts                : 0
% 1.81/2.00  # Condensation successes               : 0
% 1.81/2.00  # Termbank termtop insertions          : 3442384
% 1.81/2.01  
% 1.81/2.01  # -------------------------------------------------
% 1.81/2.01  # User time                : 1.578 s
% 1.81/2.01  # System time              : 0.078 s
% 1.81/2.01  # Total time               : 1.656 s
% 1.81/2.01  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
