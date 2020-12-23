%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0054+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:33 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 285 expanded)
%              Number of clauses        :   57 ( 136 expanded)
%              Number of leaves         :   19 (  74 expanded)
%              Depth                    :   17
%              Number of atoms          :  120 ( 316 expanded)
%              Number of equality atoms :   69 ( 255 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',idempotence_k3_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t47_xboole_1,conjecture,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(c_0_19,plain,(
    ! [X122,X123,X124] : k3_xboole_0(k3_xboole_0(X122,X123),X124) = k3_xboole_0(X122,k3_xboole_0(X123,X124)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

fof(c_0_20,plain,(
    ! [X59] : k3_xboole_0(X59,X59) = X59 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_21,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_23,plain,(
    ! [X11,X12] : k3_xboole_0(X11,X12) = k3_xboole_0(X12,X11) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_24,plain,(
    ! [X212,X213] : k4_xboole_0(X212,k2_xboole_0(X212,X213)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_25,plain,(
    ! [X9,X10] : k2_xboole_0(X9,X10) = k2_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_26,plain,(
    ! [X143,X144] : k2_xboole_0(X143,k3_xboole_0(X143,X144)) = X143 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X102,X103] :
      ( ( k4_xboole_0(X102,X103) != k1_xboole_0
        | r1_tarski(X102,X103) )
      & ( ~ r1_tarski(X102,X103)
        | k4_xboole_0(X102,X103) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_30,plain,(
    ! [X198,X199,X200] : k4_xboole_0(k4_xboole_0(X198,X199),X200) = k4_xboole_0(X198,k2_xboole_0(X199,X200)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_35,plain,(
    ! [X125,X126] : r1_tarski(k3_xboole_0(X125,X126),X125) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_41,plain,(
    ! [X141,X142] : k3_xboole_0(X141,k2_xboole_0(X141,X142)) = X141 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

fof(c_0_42,plain,(
    ! [X161,X162] :
      ( ~ r1_tarski(X161,X162)
      | k3_xboole_0(X161,X162) = X161 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_43,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | k4_xboole_0(X1,k2_xboole_0(X2,X3)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,plain,
    ( r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_21])).

cnf(c_0_46,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X1,X3))) = k3_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_34]),c_0_21]),c_0_21])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_49,plain,(
    ! [X186,X187] : r1_tarski(k4_xboole_0(X186,X187),X186) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_50,plain,
    ( r1_tarski(k4_xboole_0(k3_xboole_0(X1,k2_xboole_0(X2,X3)),X2),X3) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_51,plain,(
    ! [X192,X193] : k2_xboole_0(X192,k4_xboole_0(X193,X192)) = k2_xboole_0(X192,X193) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_52,plain,
    ( r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_34])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_46,c_0_32])).

cnf(c_0_54,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,k3_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_56,plain,(
    ! [X217,X218,X219] : k2_xboole_0(k2_xboole_0(X217,X218),X219) = k2_xboole_0(X217,k2_xboole_0(X218,X219)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_57,plain,
    ( r1_tarski(k4_xboole_0(k3_xboole_0(X1,k2_xboole_0(X2,X3)),X3),X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_32])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_59,plain,(
    ! [X228,X229] : r1_tarski(X228,k2_xboole_0(X228,X229)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_60,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X1,k2_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,k4_xboole_0(k3_xboole_0(X1,X2),X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_62,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_63,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X1,X3))) = X1 ),
    inference(spm,[status(thm)],[c_0_33,c_0_47])).

cnf(c_0_64,plain,
    ( r1_tarski(k4_xboole_0(k3_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X3,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_66,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X2,k2_xboole_0(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_28])).

cnf(c_0_67,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k3_xboole_0(X1,X2),X3)) = X1 ),
    inference(spm,[status(thm)],[c_0_33,c_0_61])).

cnf(c_0_68,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_53,c_0_62])).

cnf(c_0_69,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,k3_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_48])).

cnf(c_0_70,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_53])).

cnf(c_0_71,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_62])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,k3_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_53])).

cnf(c_0_73,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_74,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k3_xboole_0(X1,X3)))) = X1 ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_75,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X2,k2_xboole_0(X3,X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_32]),c_0_62])).

fof(c_0_76,plain,(
    ! [X207,X208,X209] :
      ( ~ r1_tarski(k4_xboole_0(X207,X208),X209)
      | r1_tarski(X207,k2_xboole_0(X208,X209)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_77,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k3_xboole_0(X1,k2_xboole_0(X3,k4_xboole_0(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_78,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_74,c_0_68])).

cnf(c_0_79,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),X3),k2_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_33])).

fof(c_0_80,plain,(
    ! [X196,X197] : k4_xboole_0(k2_xboole_0(X196,X197),X197) = k4_xboole_0(X196,X197) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_81,plain,(
    ! [X96,X97] :
      ( ( r1_tarski(X96,X97)
        | X96 != X97 )
      & ( r1_tarski(X97,X96)
        | X96 != X97 )
      & ( ~ r1_tarski(X96,X97)
        | ~ r1_tarski(X97,X96)
        | X96 = X97 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_83,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_84,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),X3),k2_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_32])).

fof(c_0_85,negated_conjecture,(
    ~ ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(assume_negation,[status(cth)],[t47_xboole_1])).

cnf(c_0_86,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_87,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_88,plain,
    ( r1_tarski(X1,k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_32])).

cnf(c_0_89,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X3)),X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_73])).

fof(c_0_90,negated_conjecture,(
    k4_xboole_0(esk16_0,k3_xboole_0(esk16_0,esk17_0)) != k4_xboole_0(esk16_0,esk17_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_85])])])).

cnf(c_0_91,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_32])).

cnf(c_0_92,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89])])).

cnf(c_0_93,negated_conjecture,
    ( k4_xboole_0(esk16_0,k3_xboole_0(esk16_0,esk17_0)) != k4_xboole_0(esk16_0,esk17_0) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_94,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_37]),c_0_39])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_94])]),
    [proof]).
%------------------------------------------------------------------------------
