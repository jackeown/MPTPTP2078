%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0204+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:40 EST 2020

% Result     : Theorem 0.59s
% Output     : CNFRefutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 252 expanded)
%              Number of clauses        :   38 (  97 expanded)
%              Number of leaves         :   21 (  77 expanded)
%              Depth                    :    9
%              Number of atoms          :   84 ( 255 expanded)
%              Number of equality atoms :   77 ( 248 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t5_boole)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k5_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t91_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t92_xboole_1)).

fof(t130_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_enumset1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d6_xboole_0)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t100_xboole_1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t21_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t16_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',idempotence_k3_xboole_0)).

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

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t3_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t17_xboole_1)).

fof(t112_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t112_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

fof(l142_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l142_enumset1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t2_boole)).

fof(c_0_21,plain,(
    ! [X321] : k5_xboole_0(X321,k1_xboole_0) = X321 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_22,plain,(
    ! [X18,X19] : k5_xboole_0(X18,X19) = k5_xboole_0(X19,X18) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_23,plain,(
    ! [X415,X416,X417] : k5_xboole_0(k5_xboole_0(X415,X416),X417) = k5_xboole_0(X415,k5_xboole_0(X416,X417)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_24,plain,(
    ! [X418] : k5_xboole_0(X418,X418) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_25,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)) ),
    inference(assume_negation,[status(cth)],[t130_enumset1])).

fof(c_0_28,plain,(
    ! [X57,X58] : k5_xboole_0(X57,X58) = k2_xboole_0(k4_xboole_0(X57,X58),k4_xboole_0(X58,X57)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

fof(c_0_29,plain,(
    ! [X430,X431] : k2_xboole_0(X430,X431) = k5_xboole_0(X430,k4_xboole_0(X431,X430)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_30,plain,(
    ! [X124,X125] : k4_xboole_0(X124,X125) = k5_xboole_0(X124,k3_xboole_0(X124,X125)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_31,plain,(
    ! [X210,X211] : k3_xboole_0(X210,k2_xboole_0(X210,X211)) = X210 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

fof(c_0_32,plain,(
    ! [X191,X192,X193] : k3_xboole_0(k3_xboole_0(X191,X192),X193) = k3_xboole_0(X191,k3_xboole_0(X192,X193)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

fof(c_0_33,plain,(
    ! [X64] : k3_xboole_0(X64,X64) = X64 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_34,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_37,negated_conjecture,(
    k7_enumset1(esk19_0,esk20_0,esk21_0,esk22_0,esk23_0,esk24_0,esk25_0,esk26_0,esk27_0) != k2_xboole_0(k2_enumset1(esk19_0,esk20_0,esk21_0,esk22_0),k3_enumset1(esk23_0,esk24_0,esk25_0,esk26_0,esk27_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

fof(c_0_38,plain,(
    ! [X794,X795,X796,X797] : k3_enumset1(X794,X794,X795,X796,X797) = k2_enumset1(X794,X795,X796,X797) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_39,plain,(
    ! [X798,X799,X800,X801,X802] : k4_enumset1(X798,X798,X799,X800,X801,X802) = k3_enumset1(X798,X799,X800,X801,X802) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_40,plain,(
    ! [X803,X804,X805,X806,X807,X808] : k5_enumset1(X803,X803,X804,X805,X806,X807,X808) = k4_enumset1(X803,X804,X805,X806,X807,X808) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_41,plain,(
    ! [X809,X810,X811,X812,X813,X814,X815] : k6_enumset1(X809,X809,X810,X811,X812,X813,X814,X815) = k5_enumset1(X809,X810,X811,X812,X813,X814,X815) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_42,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

fof(c_0_49,plain,(
    ! [X264] :
      ( ~ r1_tarski(X264,k1_xboole_0)
      | X264 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

fof(c_0_50,plain,(
    ! [X194,X195] : r1_tarski(k3_xboole_0(X194,X195),X194) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_51,plain,(
    ! [X158,X159,X160] : k5_xboole_0(k3_xboole_0(X158,X159),k3_xboole_0(X160,X159)) = k3_xboole_0(k5_xboole_0(X158,X160),X159) ),
    inference(variable_rename,[status(thm)],[t112_xboole_1])).

fof(c_0_52,plain,(
    ! [X16,X17] : k3_xboole_0(X16,X17) = k3_xboole_0(X17,X16) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_53,negated_conjecture,
    ( k7_enumset1(esk19_0,esk20_0,esk21_0,esk22_0,esk23_0,esk24_0,esk25_0,esk26_0,esk27_0) != k2_xboole_0(k2_enumset1(esk19_0,esk20_0,esk21_0,esk22_0),k3_enumset1(esk23_0,esk24_0,esk25_0,esk26_0,esk27_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_54,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_55,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_56,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_57,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_58,plain,(
    ! [X475,X476,X477,X478,X479,X480,X481,X482,X483] : k7_enumset1(X475,X476,X477,X478,X479,X480,X481,X482,X483) = k2_xboole_0(k2_enumset1(X475,X476,X477,X478),k3_enumset1(X479,X480,X481,X482,X483)) ),
    inference(variable_rename,[status(thm)],[l142_enumset1])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_44])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_43]),c_0_44])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_62,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(spm,[status(thm)],[c_0_48,c_0_26])).

cnf(c_0_63,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_64,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_65,plain,(
    ! [X235] : k3_xboole_0(X235,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_66,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_67,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_68,negated_conjecture,
    ( k7_enumset1(esk19_0,esk20_0,esk21_0,esk22_0,esk23_0,esk24_0,esk25_0,esk26_0,esk27_0) != k5_xboole_0(k6_enumset1(esk19_0,esk19_0,esk19_0,esk19_0,esk19_0,esk20_0,esk21_0,esk22_0),k5_xboole_0(k6_enumset1(esk23_0,esk23_0,esk23_0,esk23_0,esk24_0,esk25_0,esk26_0,esk27_0),k3_xboole_0(k6_enumset1(esk23_0,esk23_0,esk23_0,esk23_0,esk24_0,esk25_0,esk26_0,esk27_0),k6_enumset1(esk19_0,esk19_0,esk19_0,esk19_0,esk19_0,esk20_0,esk21_0,esk22_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_43]),c_0_44]),c_0_54]),c_0_54]),c_0_55]),c_0_55]),c_0_55]),c_0_55]),c_0_56]),c_0_56]),c_0_56]),c_0_56]),c_0_57]),c_0_57]),c_0_57]),c_0_57])).

cnf(c_0_69,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_70,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X2))))))) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_34]),c_0_34])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_46])).

cnf(c_0_72,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_73,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_74,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,k5_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_47]),c_0_26]),c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk19_0,esk19_0,esk19_0,esk19_0,esk19_0,esk20_0,esk21_0,esk22_0),k5_xboole_0(k6_enumset1(esk23_0,esk23_0,esk23_0,esk23_0,esk24_0,esk25_0,esk26_0,esk27_0),k3_xboole_0(k6_enumset1(esk19_0,esk19_0,esk19_0,esk19_0,esk19_0,esk20_0,esk21_0,esk22_0),k6_enumset1(esk23_0,esk23_0,esk23_0,esk23_0,esk24_0,esk25_0,esk26_0,esk27_0)))) != k7_enumset1(esk19_0,esk20_0,esk21_0,esk22_0,esk23_0,esk24_0,esk25_0,esk26_0,esk27_0) ),
    inference(rw,[status(thm)],[c_0_68,c_0_67])).

cnf(c_0_76,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X6,X7,X8,X9),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X6,X7,X8,X9),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_43]),c_0_44]),c_0_54]),c_0_54]),c_0_55]),c_0_55]),c_0_55]),c_0_55]),c_0_56]),c_0_56]),c_0_56]),c_0_56]),c_0_57]),c_0_57]),c_0_57]),c_0_57])).

cnf(c_0_77,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k5_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_46]),c_0_47]),c_0_46]),c_0_47]),c_0_66]),c_0_35]),c_0_72]),c_0_73]),c_0_25]),c_0_48]),c_0_26]),c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk19_0,esk19_0,esk19_0,esk19_0,esk19_0,esk20_0,esk21_0,esk22_0),k3_xboole_0(k6_enumset1(esk23_0,esk23_0,esk23_0,esk23_0,esk24_0,esk25_0,esk26_0,esk27_0),k5_xboole_0(k6_enumset1(esk19_0,esk19_0,esk19_0,esk19_0,esk19_0,esk20_0,esk21_0,esk22_0),k6_enumset1(esk23_0,esk23_0,esk23_0,esk23_0,esk24_0,esk25_0,esk26_0,esk27_0)))) != k7_enumset1(esk19_0,esk20_0,esk21_0,esk22_0,esk23_0,esk24_0,esk25_0,esk26_0,esk27_0) ),
    inference(rw,[status(thm)],[c_0_75,c_0_74])).

cnf(c_0_79,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X6,X7,X8,X9),k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X6,X7,X8,X9)))) = k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(rw,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_79])]),
    [proof]).
%------------------------------------------------------------------------------
