%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:50 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 549 expanded)
%              Number of clauses        :   67 ( 264 expanded)
%              Number of leaves         :   19 ( 141 expanded)
%              Depth                    :   15
%              Number of atoms          :  161 ( 671 expanded)
%              Number of equality atoms :   69 ( 482 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t175_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(t178_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

fof(c_0_19,plain,(
    ! [X33,X34] : k1_setfam_1(k2_tarski(X33,X34)) = k3_xboole_0(X33,X34) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_20,plain,(
    ! [X29,X30] : k1_enumset1(X29,X29,X30) = k2_tarski(X29,X30) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X5,X6] : k4_xboole_0(X5,X6) = k5_xboole_0(X5,k3_xboole_0(X5,X6)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_22,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X24,X25,X26] :
      ( ~ r1_tarski(X24,X25)
      | r1_xboole_0(X24,k4_xboole_0(X26,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_27,plain,(
    ! [X22,X23] :
      ( ( ~ r1_xboole_0(X22,X23)
        | k4_xboole_0(X22,X23) = X22 )
      & ( k4_xboole_0(X22,X23) != X22
        | r1_xboole_0(X22,X23) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_28,plain,(
    ! [X4] : k3_xboole_0(X4,X4) = X4 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_29,plain,(
    ! [X31,X32] : k3_tarski(k2_tarski(X31,X32)) = k2_xboole_0(X31,X32) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

cnf(c_0_30,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_34,plain,(
    ! [X20,X21] : r1_tarski(X20,k2_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_35,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_36,plain,(
    ! [X9] : k2_xboole_0(X9,k1_xboole_0) = X9 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_37,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(X10,X11)
      | k3_xboole_0(X10,X11) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_38,plain,(
    ! [X7,X8] : r1_tarski(k3_xboole_0(X7,X8),X7) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_39,plain,(
    ! [X27,X28] : k2_tarski(X27,X28) = k2_tarski(X28,X27) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_40,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X3,k1_setfam_1(k1_enumset1(X3,X3,X2))))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_32,c_0_31])).

cnf(c_0_42,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_33,c_0_26])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_23])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_48,plain,(
    ! [X12,X13] : r1_tarski(k4_xboole_0(X12,X13),X12) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_49,plain,(
    ! [X17] :
      ( ~ r1_tarski(X17,k1_xboole_0)
      | X17 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_50,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_53,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_42])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_55,plain,
    ( k3_tarski(k1_enumset1(X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_45,c_0_44])).

cnf(c_0_56,plain,
    ( r1_xboole_0(X1,X2)
    | k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) != X1 ),
    inference(rw,[status(thm)],[c_0_46,c_0_31])).

cnf(c_0_57,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_47,c_0_26])).

cnf(c_0_58,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_59,plain,(
    ! [X18,X19] : k4_xboole_0(X18,k4_xboole_0(X18,X19)) = k3_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_60,plain,(
    ! [X16] : k4_xboole_0(X16,k1_xboole_0) = X16 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_61,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_62,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_50,c_0_26])).

cnf(c_0_63,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_23]),c_0_23])).

cnf(c_0_64,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X3,X3))
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_66,plain,
    ( r1_xboole_0(X1,X2)
    | k5_xboole_0(X1,X1) != X1
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,X1) = X1
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_68,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))),X1) ),
    inference(rw,[status(thm)],[c_0_58,c_0_31])).

cnf(c_0_69,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_70,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_71,plain,
    ( k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_72,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_63])).

cnf(c_0_73,plain,
    ( r1_xboole_0(k5_xboole_0(X1,X1),X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_74,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_75,plain,
    ( r1_tarski(k5_xboole_0(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_42])).

fof(c_0_76,plain,(
    ! [X14,X15] : k2_xboole_0(X14,k4_xboole_0(X15,X14)) = k2_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_77,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))))) = k1_setfam_1(k1_enumset1(X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_26]),c_0_31]),c_0_31])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[c_0_70,c_0_31])).

cnf(c_0_79,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_63])).

cnf(c_0_80,plain,
    ( k5_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_72])).

cnf(c_0_81,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_67])).

cnf(c_0_82,plain,
    ( r1_xboole_0(k5_xboole_0(X1,X1),X2)
    | ~ r1_tarski(k5_xboole_0(X1,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_53]),c_0_75])])).

fof(c_0_83,plain,(
    ! [X35,X36,X37] :
      ( ~ v1_relat_1(X37)
      | k10_relat_1(X37,k2_xboole_0(X35,X36)) = k2_xboole_0(k10_relat_1(X37,X35),k10_relat_1(X37,X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).

cnf(c_0_84,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_85,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = X1
    | ~ r1_xboole_0(X1,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_77])).

cnf(c_0_86,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_87,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_80]),c_0_62])])).

cnf(c_0_88,plain,
    ( r1_xboole_0(k5_xboole_0(X1,X1),X2)
    | ~ r1_tarski(X2,k5_xboole_0(X1,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_65])])).

cnf(c_0_89,plain,
    ( k10_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_90,plain,
    ( k3_tarski(k1_enumset1(X1,X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X1))))) = k3_tarski(k1_enumset1(X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_44]),c_0_44]),c_0_31])).

cnf(c_0_91,plain,
    ( k1_xboole_0 = X1
    | ~ r1_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_79]),c_0_86])).

cnf(c_0_92,plain,
    ( r1_xboole_0(k5_xboole_0(X1,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_62])])).

fof(c_0_93,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(X1,X2)
         => r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t178_relat_1])).

cnf(c_0_94,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_63])).

cnf(c_0_95,plain,
    ( k10_relat_1(X1,k3_tarski(k1_enumset1(X2,X2,X3))) = k3_tarski(k1_enumset1(k10_relat_1(X1,X2),k10_relat_1(X1,X2),k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_44]),c_0_44])).

cnf(c_0_96,plain,
    ( k3_tarski(k1_enumset1(X1,X1,k5_xboole_0(X2,X2))) = k3_tarski(k1_enumset1(X1,X1,X2))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_57])).

cnf(c_0_97,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

fof(c_0_98,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & r1_tarski(esk1_0,esk2_0)
    & ~ r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_93])])])).

cnf(c_0_99,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k3_tarski(k1_enumset1(X3,X3,X2))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_100,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_97]),c_0_55])).

cnf(c_0_101,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_102,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_103,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_105,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_103]),c_0_104])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:22:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.45  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.19/0.45  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.45  #
% 0.19/0.45  # Preprocessing time       : 0.027 s
% 0.19/0.45  # Presaturation interreduction done
% 0.19/0.45  
% 0.19/0.45  # Proof found!
% 0.19/0.45  # SZS status Theorem
% 0.19/0.45  # SZS output start CNFRefutation
% 0.19/0.45  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.45  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.45  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.45  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 0.19/0.45  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.19/0.45  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.19/0.45  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.45  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.45  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.19/0.45  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.45  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.19/0.45  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.19/0.45  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.19/0.45  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.19/0.45  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.45  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.19/0.45  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.19/0.45  fof(t175_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 0.19/0.45  fof(t178_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 0.19/0.45  fof(c_0_19, plain, ![X33, X34]:k1_setfam_1(k2_tarski(X33,X34))=k3_xboole_0(X33,X34), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.45  fof(c_0_20, plain, ![X29, X30]:k1_enumset1(X29,X29,X30)=k2_tarski(X29,X30), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.45  fof(c_0_21, plain, ![X5, X6]:k4_xboole_0(X5,X6)=k5_xboole_0(X5,k3_xboole_0(X5,X6)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.45  cnf(c_0_22, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.45  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.45  fof(c_0_24, plain, ![X24, X25, X26]:(~r1_tarski(X24,X25)|r1_xboole_0(X24,k4_xboole_0(X26,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 0.19/0.45  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.45  cnf(c_0_26, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.45  fof(c_0_27, plain, ![X22, X23]:((~r1_xboole_0(X22,X23)|k4_xboole_0(X22,X23)=X22)&(k4_xboole_0(X22,X23)!=X22|r1_xboole_0(X22,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.19/0.45  fof(c_0_28, plain, ![X4]:k3_xboole_0(X4,X4)=X4, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.19/0.45  fof(c_0_29, plain, ![X31, X32]:k3_tarski(k2_tarski(X31,X32))=k2_xboole_0(X31,X32), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.45  cnf(c_0_30, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.45  cnf(c_0_31, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.45  cnf(c_0_32, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.45  cnf(c_0_33, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.45  fof(c_0_34, plain, ![X20, X21]:r1_tarski(X20,k2_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.45  cnf(c_0_35, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.45  fof(c_0_36, plain, ![X9]:k2_xboole_0(X9,k1_xboole_0)=X9, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.19/0.45  fof(c_0_37, plain, ![X10, X11]:(~r1_tarski(X10,X11)|k3_xboole_0(X10,X11)=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.45  fof(c_0_38, plain, ![X7, X8]:r1_tarski(k3_xboole_0(X7,X8),X7), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.19/0.45  fof(c_0_39, plain, ![X27, X28]:k2_tarski(X27,X28)=k2_tarski(X28,X27), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.19/0.45  cnf(c_0_40, plain, (r1_xboole_0(X1,k5_xboole_0(X3,k1_setfam_1(k1_enumset1(X3,X3,X2))))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.45  cnf(c_0_41, plain, (k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_32, c_0_31])).
% 0.19/0.45  cnf(c_0_42, plain, (k1_setfam_1(k1_enumset1(X1,X1,X1))=X1), inference(rw,[status(thm)],[c_0_33, c_0_26])).
% 0.19/0.45  cnf(c_0_43, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.45  cnf(c_0_44, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_35, c_0_23])).
% 0.19/0.45  cnf(c_0_45, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.45  cnf(c_0_46, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.45  cnf(c_0_47, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.45  fof(c_0_48, plain, ![X12, X13]:r1_tarski(k4_xboole_0(X12,X13),X12), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.19/0.45  fof(c_0_49, plain, ![X17]:(~r1_tarski(X17,k1_xboole_0)|X17=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.19/0.45  cnf(c_0_50, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.45  cnf(c_0_51, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.45  cnf(c_0_52, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.45  cnf(c_0_53, plain, (r1_xboole_0(X1,k5_xboole_0(X2,X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_40, c_0_42])).
% 0.19/0.45  cnf(c_0_54, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.45  cnf(c_0_55, plain, (k3_tarski(k1_enumset1(X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_45, c_0_44])).
% 0.19/0.45  cnf(c_0_56, plain, (r1_xboole_0(X1,X2)|k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))!=X1), inference(rw,[status(thm)],[c_0_46, c_0_31])).
% 0.19/0.45  cnf(c_0_57, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_47, c_0_26])).
% 0.19/0.45  cnf(c_0_58, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.45  fof(c_0_59, plain, ![X18, X19]:k4_xboole_0(X18,k4_xboole_0(X18,X19))=k3_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.45  fof(c_0_60, plain, ![X16]:k4_xboole_0(X16,k1_xboole_0)=X16, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.19/0.45  cnf(c_0_61, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.45  cnf(c_0_62, plain, (r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X2)),X1)), inference(rw,[status(thm)],[c_0_50, c_0_26])).
% 0.19/0.45  cnf(c_0_63, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_23]), c_0_23])).
% 0.19/0.45  cnf(c_0_64, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k5_xboole_0(X3,X3))|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.45  cnf(c_0_65, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.45  cnf(c_0_66, plain, (r1_xboole_0(X1,X2)|k5_xboole_0(X1,X1)!=X1|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.45  cnf(c_0_67, plain, (k5_xboole_0(X1,X1)=X1|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.45  cnf(c_0_68, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))),X1)), inference(rw,[status(thm)],[c_0_58, c_0_31])).
% 0.19/0.45  cnf(c_0_69, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.45  cnf(c_0_70, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.45  cnf(c_0_71, plain, (k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.45  cnf(c_0_72, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_57, c_0_63])).
% 0.19/0.45  cnf(c_0_73, plain, (r1_xboole_0(k5_xboole_0(X1,X1),X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.45  cnf(c_0_74, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.19/0.45  cnf(c_0_75, plain, (r1_tarski(k5_xboole_0(X1,X1),X1)), inference(spm,[status(thm)],[c_0_68, c_0_42])).
% 0.19/0.45  fof(c_0_76, plain, ![X14, X15]:k2_xboole_0(X14,k4_xboole_0(X15,X14))=k2_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.19/0.45  cnf(c_0_77, plain, (k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))))))=k1_setfam_1(k1_enumset1(X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_26]), c_0_31]), c_0_31])).
% 0.19/0.45  cnf(c_0_78, plain, (k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[c_0_70, c_0_31])).
% 0.19/0.45  cnf(c_0_79, plain, (k1_setfam_1(k1_enumset1(X1,X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_71, c_0_63])).
% 0.19/0.45  cnf(c_0_80, plain, (k5_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_41, c_0_72])).
% 0.19/0.45  cnf(c_0_81, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_73, c_0_67])).
% 0.19/0.45  cnf(c_0_82, plain, (r1_xboole_0(k5_xboole_0(X1,X1),X2)|~r1_tarski(k5_xboole_0(X1,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_53]), c_0_75])])).
% 0.19/0.45  fof(c_0_83, plain, ![X35, X36, X37]:(~v1_relat_1(X37)|k10_relat_1(X37,k2_xboole_0(X35,X36))=k2_xboole_0(k10_relat_1(X37,X35),k10_relat_1(X37,X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).
% 0.19/0.45  cnf(c_0_84, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.19/0.45  cnf(c_0_85, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=X1|~r1_xboole_0(X1,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))))), inference(spm,[status(thm)],[c_0_41, c_0_77])).
% 0.19/0.45  cnf(c_0_86, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_78, c_0_79])).
% 0.19/0.45  cnf(c_0_87, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_80]), c_0_62])])).
% 0.19/0.45  cnf(c_0_88, plain, (r1_xboole_0(k5_xboole_0(X1,X1),X2)|~r1_tarski(X2,k5_xboole_0(X1,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_65])])).
% 0.19/0.45  cnf(c_0_89, plain, (k10_relat_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.19/0.45  cnf(c_0_90, plain, (k3_tarski(k1_enumset1(X1,X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X1)))))=k3_tarski(k1_enumset1(X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_44]), c_0_44]), c_0_31])).
% 0.19/0.45  cnf(c_0_91, plain, (k1_xboole_0=X1|~r1_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_79]), c_0_86])).
% 0.19/0.45  cnf(c_0_92, plain, (r1_xboole_0(k5_xboole_0(X1,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_62])])).
% 0.19/0.45  fof(c_0_93, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))))), inference(assume_negation,[status(cth)],[t178_relat_1])).
% 0.19/0.45  cnf(c_0_94, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X1)))), inference(spm,[status(thm)],[c_0_54, c_0_63])).
% 0.19/0.45  cnf(c_0_95, plain, (k10_relat_1(X1,k3_tarski(k1_enumset1(X2,X2,X3)))=k3_tarski(k1_enumset1(k10_relat_1(X1,X2),k10_relat_1(X1,X2),k10_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_44]), c_0_44])).
% 0.19/0.45  cnf(c_0_96, plain, (k3_tarski(k1_enumset1(X1,X1,k5_xboole_0(X2,X2)))=k3_tarski(k1_enumset1(X1,X1,X2))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_90, c_0_57])).
% 0.19/0.45  cnf(c_0_97, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.19/0.45  fof(c_0_98, negated_conjecture, (v1_relat_1(esk3_0)&(r1_tarski(esk1_0,esk2_0)&~r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_93])])])).
% 0.19/0.45  cnf(c_0_99, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k3_tarski(k1_enumset1(X3,X3,X2))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.19/0.45  cnf(c_0_100, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=X1|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_97]), c_0_55])).
% 0.19/0.45  cnf(c_0_101, negated_conjecture, (~r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.19/0.45  cnf(c_0_102, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 0.19/0.45  cnf(c_0_103, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.19/0.45  cnf(c_0_104, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.19/0.45  cnf(c_0_105, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_103]), c_0_104])]), ['proof']).
% 0.19/0.45  # SZS output end CNFRefutation
% 0.19/0.45  # Proof object total steps             : 106
% 0.19/0.45  # Proof object clause steps            : 67
% 0.19/0.45  # Proof object formula steps           : 39
% 0.19/0.45  # Proof object conjectures             : 7
% 0.19/0.45  # Proof object clause conjectures      : 4
% 0.19/0.45  # Proof object formula conjectures     : 3
% 0.19/0.45  # Proof object initial clauses used    : 22
% 0.19/0.45  # Proof object initial formulas used   : 19
% 0.19/0.45  # Proof object generating inferences   : 26
% 0.19/0.45  # Proof object simplifying inferences  : 38
% 0.19/0.45  # Training examples: 0 positive, 0 negative
% 0.19/0.45  # Parsed axioms                        : 19
% 0.19/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.45  # Initial clauses                      : 22
% 0.19/0.45  # Removed in clause preprocessing      : 4
% 0.19/0.45  # Initial clauses in saturation        : 18
% 0.19/0.45  # Processed clauses                    : 1432
% 0.19/0.45  # ...of these trivial                  : 25
% 0.19/0.45  # ...subsumed                          : 1144
% 0.19/0.45  # ...remaining for further processing  : 263
% 0.19/0.45  # Other redundant clauses eliminated   : 51
% 0.19/0.45  # Clauses deleted for lack of memory   : 0
% 0.19/0.45  # Backward-subsumed                    : 21
% 0.19/0.45  # Backward-rewritten                   : 17
% 0.19/0.45  # Generated clauses                    : 4692
% 0.19/0.45  # ...of the previous two non-trivial   : 3571
% 0.19/0.45  # Contextual simplify-reflections      : 4
% 0.19/0.45  # Paramodulations                      : 4641
% 0.19/0.45  # Factorizations                       : 0
% 0.19/0.45  # Equation resolutions                 : 51
% 0.19/0.45  # Propositional unsat checks           : 0
% 0.19/0.45  #    Propositional check models        : 0
% 0.19/0.45  #    Propositional check unsatisfiable : 0
% 0.19/0.45  #    Propositional clauses             : 0
% 0.19/0.45  #    Propositional clauses after purity: 0
% 0.19/0.45  #    Propositional unsat core size     : 0
% 0.19/0.45  #    Propositional preprocessing time  : 0.000
% 0.19/0.45  #    Propositional encoding time       : 0.000
% 0.19/0.45  #    Propositional solver time         : 0.000
% 0.19/0.45  #    Success case prop preproc time    : 0.000
% 0.19/0.45  #    Success case prop encoding time   : 0.000
% 0.19/0.45  #    Success case prop solver time     : 0.000
% 0.19/0.45  # Current number of processed clauses  : 207
% 0.19/0.45  #    Positive orientable unit clauses  : 34
% 0.19/0.45  #    Positive unorientable unit clauses: 1
% 0.19/0.45  #    Negative unit clauses             : 2
% 0.19/0.45  #    Non-unit-clauses                  : 170
% 0.19/0.45  # Current number of unprocessed clauses: 2082
% 0.19/0.45  # ...number of literals in the above   : 5384
% 0.19/0.45  # Current number of archived formulas  : 0
% 0.19/0.45  # Current number of archived clauses   : 60
% 0.19/0.45  # Clause-clause subsumption calls (NU) : 12813
% 0.19/0.45  # Rec. Clause-clause subsumption calls : 9876
% 0.19/0.45  # Non-unit clause-clause subsumptions  : 948
% 0.19/0.45  # Unit Clause-clause subsumption calls : 95
% 0.19/0.45  # Rewrite failures with RHS unbound    : 0
% 0.19/0.45  # BW rewrite match attempts            : 138
% 0.19/0.45  # BW rewrite match successes           : 18
% 0.19/0.45  # Condensation attempts                : 0
% 0.19/0.45  # Condensation successes               : 0
% 0.19/0.45  # Termbank termtop insertions          : 61068
% 0.19/0.45  
% 0.19/0.45  # -------------------------------------------------
% 0.19/0.45  # User time                : 0.099 s
% 0.19/0.45  # System time              : 0.010 s
% 0.19/0.45  # Total time               : 0.109 s
% 0.19/0.45  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
