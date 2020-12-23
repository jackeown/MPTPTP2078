%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0137+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:37 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 639 expanded)
%              Number of clauses        :   47 ( 270 expanded)
%              Number of leaves         :   20 ( 184 expanded)
%              Depth                    :   11
%              Number of atoms          :   93 ( 649 expanded)
%              Number of equality atoms :   84 ( 632 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t49_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t100_xboole_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t22_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t98_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t51_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t16_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t91_xboole_1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t95_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t79_xboole_1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t21_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',idempotence_k3_xboole_0)).

fof(t53_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_enumset1)).

fof(t51_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(t93_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t93_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d7_xboole_0)).

fof(t112_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t112_xboole_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k5_xboole_0)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t5_boole)).

fof(l62_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

fof(c_0_20,plain,(
    ! [X284,X285,X286] : k3_xboole_0(X284,k4_xboole_0(X285,X286)) = k4_xboole_0(k3_xboole_0(X284,X285),X286) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_21,plain,(
    ! [X121,X122] : k4_xboole_0(X121,X122) = k5_xboole_0(X121,k3_xboole_0(X121,X122)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_22,plain,(
    ! [X209,X210] : k2_xboole_0(X209,k3_xboole_0(X209,X210)) = X209 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

fof(c_0_23,plain,(
    ! [X427,X428] : k2_xboole_0(X427,X428) = k5_xboole_0(X427,k4_xboole_0(X428,X427)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_24,plain,(
    ! [X294,X295] : k2_xboole_0(k3_xboole_0(X294,X295),k4_xboole_0(X294,X295)) = X294 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_27,plain,(
    ! [X188,X189,X190] : k3_xboole_0(k3_xboole_0(X188,X189),X190) = k3_xboole_0(X188,k3_xboole_0(X189,X190)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_31,plain,(
    ! [X13,X14] : k3_xboole_0(X13,X14) = k3_xboole_0(X14,X13) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_32,plain,(
    ! [X412,X413,X414] : k5_xboole_0(k5_xboole_0(X412,X413),X414) = k5_xboole_0(X412,k5_xboole_0(X413,X414)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_26])).

cnf(c_0_34,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_26])).

fof(c_0_36,plain,(
    ! [X420,X421] : k3_xboole_0(X420,X421) = k5_xboole_0(k5_xboole_0(X420,X421),k2_xboole_0(X420,X421)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

fof(c_0_37,plain,(
    ! [X373,X374] : r1_xboole_0(k4_xboole_0(X373,X374),X374) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_38,plain,(
    ! [X207,X208] : k3_xboole_0(X207,k2_xboole_0(X207,X208)) = X207 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

fof(c_0_39,plain,(
    ! [X61] : k3_xboole_0(X61,X61) = X61 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_40,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(X1,X2)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_29]),c_0_26]),c_0_26])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3))) = k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_44,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X1)))) = X1 ),
    inference(rw,[status(thm)],[c_0_35,c_0_34])).

fof(c_0_45,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(assume_negation,[status(cth)],[t53_enumset1])).

fof(c_0_46,plain,(
    ! [X519,X520,X521,X522,X523,X524] : k4_enumset1(X519,X520,X521,X522,X523,X524) = k2_xboole_0(k1_tarski(X519),k3_enumset1(X520,X521,X522,X523,X524)) ),
    inference(variable_rename,[status(thm)],[t51_enumset1])).

fof(c_0_47,plain,(
    ! [X416,X417] : k2_xboole_0(X416,X417) = k2_xboole_0(k5_xboole_0(X416,X417),k3_xboole_0(X416,X417)) ),
    inference(variable_rename,[status(thm)],[t93_xboole_1])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_49,plain,(
    ! [X56,X57] :
      ( ( ~ r1_xboole_0(X56,X57)
        | k3_xboole_0(X56,X57) = k1_xboole_0 )
      & ( k3_xboole_0(X56,X57) != k1_xboole_0
        | r1_xboole_0(X56,X57) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_50,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_51,plain,(
    ! [X155,X156,X157] : k5_xboole_0(k3_xboole_0(X155,X156),k3_xboole_0(X157,X156)) = k3_xboole_0(k5_xboole_0(X155,X157),X156) ),
    inference(variable_rename,[status(thm)],[t112_xboole_1])).

fof(c_0_52,plain,(
    ! [X15,X16] : k5_xboole_0(X15,X16) = k5_xboole_0(X16,X15) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_54,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_55,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))))))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_34]),c_0_42]),c_0_43])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = X1 ),
    inference(rw,[status(thm)],[c_0_44,c_0_43])).

fof(c_0_57,negated_conjecture,(
    k4_enumset1(esk19_0,esk20_0,esk21_0,esk22_0,esk23_0,esk24_0) != k2_xboole_0(k1_enumset1(esk19_0,esk20_0,esk21_0),k1_enumset1(esk22_0,esk23_0,esk24_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_45])])])).

cnf(c_0_58,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_59,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_29]),c_0_26])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_62,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_50,c_0_26])).

fof(c_0_63,plain,(
    ! [X318] : k5_xboole_0(X318,k1_xboole_0) = X318 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_64,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_65,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_66,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_29]),c_0_26])).

cnf(c_0_67,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_54])).

cnf(c_0_68,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_69,negated_conjecture,
    ( k4_enumset1(esk19_0,esk20_0,esk21_0,esk22_0,esk23_0,esk24_0) != k2_xboole_0(k1_enumset1(esk19_0,esk20_0,esk21_0),k1_enumset1(esk22_0,esk23_0,esk24_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_70,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_tarski(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_29]),c_0_26])).

fof(c_0_71,plain,(
    ! [X473,X474,X475,X476,X477,X478] : k4_enumset1(X473,X474,X475,X476,X477,X478) = k2_xboole_0(k1_enumset1(X473,X474,X475),k1_enumset1(X476,X477,X478)) ),
    inference(variable_rename,[status(thm)],[l62_enumset1])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_29]),c_0_29]),c_0_26]),c_0_26])).

cnf(c_0_73,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_60,c_0_42])).

cnf(c_0_74,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_41])).

cnf(c_0_75,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_76,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,k5_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_54]),c_0_65]),c_0_41])).

cnf(c_0_77,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_34]),c_0_68])).

cnf(c_0_78,negated_conjecture,
    ( k5_xboole_0(k1_tarski(esk19_0),k5_xboole_0(k3_enumset1(esk20_0,esk21_0,esk22_0,esk23_0,esk24_0),k3_xboole_0(k3_enumset1(esk20_0,esk21_0,esk22_0,esk23_0,esk24_0),k1_tarski(esk19_0)))) != k5_xboole_0(k1_enumset1(esk19_0,esk20_0,esk21_0),k5_xboole_0(k1_enumset1(esk22_0,esk23_0,esk24_0),k3_xboole_0(k1_enumset1(esk22_0,esk23_0,esk24_0),k1_enumset1(esk19_0,esk20_0,esk21_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_29]),c_0_26]),c_0_70])).

cnf(c_0_79,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_80,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X1,X2)))))) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_34]),c_0_43]),c_0_42])).

cnf(c_0_81,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,X1))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_64]),c_0_41]),c_0_74]),c_0_75]),c_0_65]),c_0_76]),c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( k5_xboole_0(k1_tarski(esk19_0),k5_xboole_0(k3_enumset1(esk20_0,esk21_0,esk22_0,esk23_0,esk24_0),k3_xboole_0(k1_tarski(esk19_0),k3_enumset1(esk20_0,esk21_0,esk22_0,esk23_0,esk24_0)))) != k5_xboole_0(k1_enumset1(esk19_0,esk20_0,esk21_0),k5_xboole_0(k1_enumset1(esk22_0,esk23_0,esk24_0),k3_xboole_0(k1_enumset1(esk19_0,esk20_0,esk21_0),k1_enumset1(esk22_0,esk23_0,esk24_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_41]),c_0_41])).

cnf(c_0_83,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_tarski(X1)))) = k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_29]),c_0_26]),c_0_70])).

cnf(c_0_84,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_81]),c_0_77]),c_0_76])).

cnf(c_0_85,negated_conjecture,
    ( k5_xboole_0(k1_tarski(esk19_0),k3_xboole_0(k3_enumset1(esk20_0,esk21_0,esk22_0,esk23_0,esk24_0),k5_xboole_0(k1_tarski(esk19_0),k3_enumset1(esk20_0,esk21_0,esk22_0,esk23_0,esk24_0)))) != k5_xboole_0(k1_enumset1(esk19_0,esk20_0,esk21_0),k3_xboole_0(k1_enumset1(esk22_0,esk23_0,esk24_0),k5_xboole_0(k1_enumset1(esk19_0,esk20_0,esk21_0),k1_enumset1(esk22_0,esk23_0,esk24_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_76]),c_0_76])).

cnf(c_0_86,plain,
    ( k5_xboole_0(k1_tarski(X1),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k5_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)))) = k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X4,X5,X6),k5_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_84]),c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_86])]),
    [proof]).
%------------------------------------------------------------------------------
