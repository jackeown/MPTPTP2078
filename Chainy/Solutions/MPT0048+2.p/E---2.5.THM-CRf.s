%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0048+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:33 EST 2020

% Result     : Theorem 15.72s
% Output     : CNFRefutation 15.72s
% Verified   : 
% Statistics : Number of formulae       :  131 (3122 expanded)
%              Number of clauses        :   84 (1455 expanded)
%              Number of leaves         :   23 ( 833 expanded)
%              Depth                    :   23
%              Number of atoms          :  166 (3414 expanded)
%              Number of equality atoms :  108 (2839 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t23_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(t24_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).

fof(t38_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k4_xboole_0(X2,X1))
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k4_xboole_0(X2,X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',idempotence_k3_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t6_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(t41_xboole_1,conjecture,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(c_0_23,plain,(
    ! [X133] : k2_xboole_0(X133,k1_xboole_0) = X133 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_24,plain,(
    ! [X9,X10] : k2_xboole_0(X9,X10) = k2_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_25,plain,(
    ! [X196,X197] : k4_xboole_0(k2_xboole_0(X196,X197),X197) = k4_xboole_0(X196,X197) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_26,plain,(
    ! [X143,X144] : k2_xboole_0(X143,k3_xboole_0(X143,X144)) = X143 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

fof(c_0_27,plain,(
    ! [X11,X12] : k3_xboole_0(X11,X12) = k3_xboole_0(X12,X11) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X201] : k4_xboole_0(k1_xboole_0,X201) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_31,plain,(
    ! [X202,X203,X204] : k2_xboole_0(k2_xboole_0(X202,X203),X204) = k2_xboole_0(X202,k2_xboole_0(X203,X204)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_32,plain,(
    ! [X192,X193] : k2_xboole_0(X192,k4_xboole_0(X193,X192)) = k2_xboole_0(X192,X193) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_33,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_38,plain,(
    ! [X141,X142] : k3_xboole_0(X141,k2_xboole_0(X141,X142)) = X141 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

cnf(c_0_39,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_29])).

cnf(c_0_42,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_36]),c_0_37])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X1),X3)) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_39])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X2) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_44,c_0_29])).

fof(c_0_48,plain,(
    ! [X134,X135,X136] :
      ( ~ r1_tarski(X134,X135)
      | ~ r1_tarski(X135,X136)
      | r1_tarski(X134,X136) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_49,plain,(
    ! [X186,X187] : r1_tarski(k4_xboole_0(X186,X187),X186) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_50,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X3),X2) = k4_xboole_0(k2_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_45]),c_0_41])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_52,plain,(
    ! [X213,X214] : r1_tarski(X213,k2_xboole_0(X213,X214)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_55,plain,(
    ! [X125,X126] : r1_tarski(k3_xboole_0(X125,X126),X125) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_56,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1)) = k4_xboole_0(X2,k2_xboole_0(X3,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_36])).

fof(c_0_57,plain,(
    ! [X102,X103] :
      ( ( k4_xboole_0(X102,X103) != k1_xboole_0
        | r1_tarski(X102,X103) )
      & ( ~ r1_tarski(X102,X103)
        | k4_xboole_0(X102,X103) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_59,plain,(
    ! [X145,X146,X147] : k3_xboole_0(X145,k2_xboole_0(X146,X147)) = k2_xboole_0(k3_xboole_0(X145,X146),k3_xboole_0(X145,X147)) ),
    inference(variable_rename,[status(thm)],[t23_xboole_1])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_62,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X3,X2)) = k4_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_40]),c_0_56])).

cnf(c_0_63,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_29])).

cnf(c_0_65,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_66,plain,(
    ! [X148,X149,X150] : k2_xboole_0(X148,k3_xboole_0(X149,X150)) = k3_xboole_0(k2_xboole_0(X148,X149),k2_xboole_0(X148,X150)) ),
    inference(variable_rename,[status(thm)],[t24_xboole_1])).

fof(c_0_67,plain,(
    ! [X190,X191] :
      ( ~ r1_tarski(X190,k4_xboole_0(X191,X190))
      | X190 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).

cnf(c_0_68,plain,
    ( r1_tarski(k3_xboole_0(k4_xboole_0(X1,X2),X3),X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_69,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k3_xboole_0(X2,X3)),X3) = k4_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_62,c_0_42])).

cnf(c_0_70,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_63]),c_0_28])).

cnf(c_0_71,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X1,k2_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_72,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_73,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_74,plain,
    ( r1_tarski(k3_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X1,k3_xboole_0(X4,X2))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_75,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(k4_xboole_0(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_70])).

cnf(c_0_76,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_54])).

cnf(c_0_77,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_39])).

cnf(c_0_78,plain,
    ( r1_tarski(k3_xboole_0(k2_xboole_0(X1,X2),X3),k2_xboole_0(X1,k3_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_79,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_35])).

cnf(c_0_80,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_47,c_0_39])).

cnf(c_0_81,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_82,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X3,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_42])).

fof(c_0_83,plain,(
    ! [X161,X162] :
      ( ~ r1_tarski(X161,X162)
      | k3_xboole_0(X161,X162) = X161 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_84,plain,
    ( r1_tarski(k3_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X2)),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_28])).

cnf(c_0_85,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X3,X1)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_86,plain,
    ( k4_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,X3)),X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_82,c_0_34])).

cnf(c_0_87,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_88,plain,
    ( r1_tarski(k3_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X2,X1))),X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_40])).

cnf(c_0_89,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X3)) = k4_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_85])).

fof(c_0_90,plain,(
    ! [X174,X175] :
      ( k4_xboole_0(X174,X175) != k4_xboole_0(X175,X174)
      | X174 = X175 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_xboole_1])])).

cnf(c_0_91,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_92,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_93,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X2,k2_xboole_0(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_35])).

cnf(c_0_94,plain,
    ( X1 = X2
    | k4_xboole_0(X1,X2) != k4_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_95,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k3_xboole_0(X2,X3))),X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_96,plain,
    ( k3_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X1),X3)) = k3_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_79]),c_0_36])).

fof(c_0_97,plain,(
    ! [X59] : k3_xboole_0(X59,X59) = X59 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_98,plain,
    ( r1_tarski(X1,k3_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_93,c_0_47])).

cnf(c_0_99,plain,
    ( k2_xboole_0(X1,X2) = X2
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_33]),c_0_51])).

cnf(c_0_100,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_95,c_0_80])).

cnf(c_0_101,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_35])).

cnf(c_0_102,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_40]),c_0_96])).

cnf(c_0_103,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_40])).

cnf(c_0_104,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_81]),c_0_35])).

cnf(c_0_105,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

fof(c_0_106,plain,(
    ! [X96,X97] :
      ( ( r1_tarski(X96,X97)
        | X96 != X97 )
      & ( r1_tarski(X97,X96)
        | X96 != X97 )
      & ( ~ r1_tarski(X96,X97)
        | ~ r1_tarski(X97,X96)
        | X96 = X97 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_107,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k3_xboole_0(X1,k2_xboole_0(X3,k4_xboole_0(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_98,c_0_81])).

cnf(c_0_108,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_29])).

cnf(c_0_109,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

fof(c_0_110,plain,(
    ! [X209,X210] : k2_xboole_0(X209,k2_xboole_0(X209,X210)) = k2_xboole_0(X209,X210) ),
    inference(variable_rename,[status(thm)],[t6_xboole_1])).

cnf(c_0_111,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_29])).

cnf(c_0_112,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_102]),c_0_105])).

cnf(c_0_113,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_114,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_115,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_109,c_0_35])).

cnf(c_0_116,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X3) = k4_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_39])).

cnf(c_0_117,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_110])).

cnf(c_0_118,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[c_0_111,c_0_112])).

cnf(c_0_119,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_115])])).

cnf(c_0_120,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3)) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_33])).

fof(c_0_121,negated_conjecture,(
    ~ ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(assume_negation,[status(cth)],[t41_xboole_1])).

cnf(c_0_122,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_81])).

cnf(c_0_123,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) = k4_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_120,c_0_29])).

fof(c_0_124,negated_conjecture,(
    k4_xboole_0(k4_xboole_0(esk16_0,esk17_0),esk18_0) != k4_xboole_0(esk16_0,k2_xboole_0(esk17_0,esk18_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_121])])])).

cnf(c_0_125,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X1),X3)) = k4_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_96]),c_0_122])).

cnf(c_0_126,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_103,c_0_112])).

cnf(c_0_127,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X2,X3)) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_40]),c_0_123])).

cnf(c_0_128,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk16_0,esk17_0),esk18_0) != k4_xboole_0(esk16_0,k2_xboole_0(esk17_0,esk18_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_124])).

cnf(c_0_129,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_127])).

cnf(c_0_130,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_128,c_0_129])]),
    [proof]).
%------------------------------------------------------------------------------
