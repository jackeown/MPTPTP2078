%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0313+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:42 EST 2020

% Result     : Theorem 14.22s
% Output     : CNFRefutation 14.22s
% Verified   : 
% Statistics : Number of formulae       :  119 (3070 expanded)
%              Number of clauses        :   70 (1203 expanded)
%              Number of leaves         :   24 ( 933 expanded)
%              Depth                    :   14
%              Number of atoms          :  145 (3145 expanded)
%              Number of equality atoms :  144 (3144 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t70_enumset1)).

fof(t125_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k4_xboole_0(X1,X2)) = k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t95_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t72_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t100_xboole_1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t75_enumset1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',idempotence_k3_xboole_0)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',idempotence_k2_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t91_xboole_1)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t92_xboole_1)).

fof(t122_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k3_xboole_0(X1,X2),X3) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_zfmisc_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k5_xboole_0)).

fof(t68_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t68_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t69_enumset1)).

fof(t134_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t134_enumset1)).

fof(t93_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t93_xboole_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t5_boole)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t1_boole)).

fof(c_0_24,plain,(
    ! [X1078,X1079] : k3_tarski(k2_tarski(X1078,X1079)) = k2_xboole_0(X1078,X1079) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_25,plain,(
    ! [X892,X893] : k1_enumset1(X892,X892,X893) = k2_tarski(X892,X893) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & k2_zfmisc_1(X3,k4_xboole_0(X1,X2)) = k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    inference(assume_negation,[status(cth)],[t125_zfmisc_1])).

fof(c_0_27,plain,(
    ! [X426,X427] : k3_xboole_0(X426,X427) = k5_xboole_0(k5_xboole_0(X426,X427),k2_xboole_0(X426,X427)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_28,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_30,plain,(
    ! [X894,X895,X896] : k2_enumset1(X894,X894,X895,X896) = k1_enumset1(X894,X895,X896) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_31,plain,(
    ! [X897,X898,X899,X900] : k3_enumset1(X897,X897,X898,X899,X900) = k2_enumset1(X897,X898,X899,X900) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_32,negated_conjecture,
    ( k2_zfmisc_1(k4_xboole_0(esk47_0,esk48_0),esk49_0) != k4_xboole_0(k2_zfmisc_1(esk47_0,esk49_0),k2_zfmisc_1(esk48_0,esk49_0))
    | k2_zfmisc_1(esk49_0,k4_xboole_0(esk47_0,esk48_0)) != k4_xboole_0(k2_zfmisc_1(esk49_0,esk47_0),k2_zfmisc_1(esk49_0,esk48_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

fof(c_0_33,plain,(
    ! [X127,X128] : k4_xboole_0(X127,X128) = k5_xboole_0(X127,k3_xboole_0(X127,X128)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_38,plain,(
    ! [X901,X902,X903,X904,X905] : k4_enumset1(X901,X901,X902,X903,X904,X905) = k3_enumset1(X901,X902,X903,X904,X905) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_39,plain,(
    ! [X906,X907,X908,X909,X910,X911] : k5_enumset1(X906,X906,X907,X908,X909,X910,X911) = k4_enumset1(X906,X907,X908,X909,X910,X911) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_40,plain,(
    ! [X912,X913,X914,X915,X916,X917,X918] : k6_enumset1(X912,X912,X913,X914,X915,X916,X917,X918) = k5_enumset1(X912,X913,X914,X915,X916,X917,X918) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_41,plain,(
    ! [X67] : k3_xboole_0(X67,X67) = X67 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_42,plain,(
    ! [X66] : k2_xboole_0(X66,X66) = X66 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_43,negated_conjecture,
    ( k2_zfmisc_1(k4_xboole_0(esk47_0,esk48_0),esk49_0) != k4_xboole_0(k2_zfmisc_1(esk47_0,esk49_0),k2_zfmisc_1(esk48_0,esk49_0))
    | k2_zfmisc_1(esk49_0,k4_xboole_0(esk47_0,esk48_0)) != k4_xboole_0(k2_zfmisc_1(esk49_0,esk47_0),k2_zfmisc_1(esk49_0,esk48_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_46,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_49,plain,(
    ! [X418,X419,X420] : k5_xboole_0(k5_xboole_0(X418,X419),X420) = k5_xboole_0(X418,k5_xboole_0(X419,X420)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_50,plain,(
    ! [X1139,X1140,X1141] :
      ( k2_zfmisc_1(k2_xboole_0(X1139,X1140),X1141) = k2_xboole_0(k2_zfmisc_1(X1139,X1141),k2_zfmisc_1(X1140,X1141))
      & k2_zfmisc_1(X1141,k2_xboole_0(X1139,X1140)) = k2_xboole_0(k2_zfmisc_1(X1141,X1139),k2_zfmisc_1(X1141,X1140)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_52,plain,(
    ! [X421] : k5_xboole_0(X421,X421) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_53,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( k2_zfmisc_1(esk49_0,k5_xboole_0(esk47_0,k5_xboole_0(k5_xboole_0(esk47_0,esk48_0),k3_tarski(k6_enumset1(esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk48_0))))) != k5_xboole_0(k2_zfmisc_1(esk49_0,esk47_0),k5_xboole_0(k5_xboole_0(k2_zfmisc_1(esk49_0,esk47_0),k2_zfmisc_1(esk49_0,esk48_0)),k3_tarski(k6_enumset1(k2_zfmisc_1(esk49_0,esk47_0),k2_zfmisc_1(esk49_0,esk47_0),k2_zfmisc_1(esk49_0,esk47_0),k2_zfmisc_1(esk49_0,esk47_0),k2_zfmisc_1(esk49_0,esk47_0),k2_zfmisc_1(esk49_0,esk47_0),k2_zfmisc_1(esk49_0,esk47_0),k2_zfmisc_1(esk49_0,esk48_0)))))
    | k2_zfmisc_1(k5_xboole_0(esk47_0,k5_xboole_0(k5_xboole_0(esk47_0,esk48_0),k3_tarski(k6_enumset1(esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk48_0)))),esk49_0) != k5_xboole_0(k2_zfmisc_1(esk47_0,esk49_0),k5_xboole_0(k5_xboole_0(k2_zfmisc_1(esk47_0,esk49_0),k2_zfmisc_1(esk48_0,esk49_0)),k3_tarski(k6_enumset1(k2_zfmisc_1(esk47_0,esk49_0),k2_zfmisc_1(esk47_0,esk49_0),k2_zfmisc_1(esk47_0,esk49_0),k2_zfmisc_1(esk47_0,esk49_0),k2_zfmisc_1(esk47_0,esk49_0),k2_zfmisc_1(esk47_0,esk49_0),k2_zfmisc_1(esk47_0,esk49_0),k2_zfmisc_1(esk48_0,esk49_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_48]),c_0_48])).

cnf(c_0_55,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_57,plain,(
    ! [X1146,X1147,X1148] :
      ( k2_zfmisc_1(k3_xboole_0(X1146,X1147),X1148) = k3_xboole_0(k2_zfmisc_1(X1146,X1148),k2_zfmisc_1(X1147,X1148))
      & k2_zfmisc_1(X1148,k3_xboole_0(X1146,X1147)) = k3_xboole_0(k2_zfmisc_1(X1148,X1146),k2_zfmisc_1(X1148,X1147)) ) ),
    inference(variable_rename,[status(thm)],[t122_zfmisc_1])).

cnf(c_0_58,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_45]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_35]),c_0_36]),c_0_37]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_61,negated_conjecture,
    ( k5_xboole_0(k2_zfmisc_1(esk49_0,esk47_0),k5_xboole_0(k2_zfmisc_1(esk49_0,esk47_0),k5_xboole_0(k2_zfmisc_1(esk49_0,esk48_0),k3_tarski(k6_enumset1(k2_zfmisc_1(esk49_0,esk47_0),k2_zfmisc_1(esk49_0,esk47_0),k2_zfmisc_1(esk49_0,esk47_0),k2_zfmisc_1(esk49_0,esk47_0),k2_zfmisc_1(esk49_0,esk47_0),k2_zfmisc_1(esk49_0,esk47_0),k2_zfmisc_1(esk49_0,esk47_0),k2_zfmisc_1(esk49_0,esk48_0)))))) != k2_zfmisc_1(esk49_0,k5_xboole_0(esk47_0,k5_xboole_0(esk47_0,k5_xboole_0(esk48_0,k3_tarski(k6_enumset1(esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk48_0))))))
    | k5_xboole_0(k2_zfmisc_1(esk47_0,esk49_0),k5_xboole_0(k2_zfmisc_1(esk47_0,esk49_0),k5_xboole_0(k2_zfmisc_1(esk48_0,esk49_0),k3_tarski(k6_enumset1(k2_zfmisc_1(esk47_0,esk49_0),k2_zfmisc_1(esk47_0,esk49_0),k2_zfmisc_1(esk47_0,esk49_0),k2_zfmisc_1(esk47_0,esk49_0),k2_zfmisc_1(esk47_0,esk49_0),k2_zfmisc_1(esk47_0,esk49_0),k2_zfmisc_1(esk47_0,esk49_0),k2_zfmisc_1(esk48_0,esk49_0)))))) != k2_zfmisc_1(k5_xboole_0(esk47_0,k5_xboole_0(esk47_0,k5_xboole_0(esk48_0,k3_tarski(k6_enumset1(esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk48_0))))),esk49_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55]),c_0_55]),c_0_55]),c_0_55])).

cnf(c_0_62,plain,
    ( k2_zfmisc_1(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) = k3_tarski(k6_enumset1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48])).

cnf(c_0_63,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_64,plain,
    ( k2_zfmisc_1(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

fof(c_0_66,plain,(
    ! [X21,X22] : k5_xboole_0(X21,X22) = k5_xboole_0(X22,X21) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_67,negated_conjecture,
    ( k5_xboole_0(k2_zfmisc_1(esk47_0,esk49_0),k5_xboole_0(k2_zfmisc_1(esk47_0,esk49_0),k5_xboole_0(k2_zfmisc_1(esk48_0,esk49_0),k3_tarski(k6_enumset1(k2_zfmisc_1(esk47_0,esk49_0),k2_zfmisc_1(esk47_0,esk49_0),k2_zfmisc_1(esk47_0,esk49_0),k2_zfmisc_1(esk47_0,esk49_0),k2_zfmisc_1(esk47_0,esk49_0),k2_zfmisc_1(esk47_0,esk49_0),k2_zfmisc_1(esk47_0,esk49_0),k2_zfmisc_1(esk48_0,esk49_0)))))) != k2_zfmisc_1(k5_xboole_0(esk47_0,k5_xboole_0(esk47_0,k5_xboole_0(esk48_0,k3_tarski(k6_enumset1(esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk48_0))))),esk49_0)
    | k5_xboole_0(k2_zfmisc_1(esk49_0,esk47_0),k5_xboole_0(k2_zfmisc_1(esk49_0,esk47_0),k5_xboole_0(k2_zfmisc_1(esk49_0,esk48_0),k2_zfmisc_1(esk49_0,k3_tarski(k6_enumset1(esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk48_0)))))) != k2_zfmisc_1(esk49_0,k5_xboole_0(esk47_0,k5_xboole_0(esk47_0,k5_xboole_0(esk48_0,k3_tarski(k6_enumset1(esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk48_0)))))) ),
    inference(rw,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_68,plain,
    ( k2_zfmisc_1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X3) = k3_tarski(k6_enumset1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48])).

cnf(c_0_69,plain,
    ( k2_zfmisc_1(X1,k5_xboole_0(k5_xboole_0(X2,X3),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))) = k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)),k3_tarski(k6_enumset1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48])).

cnf(c_0_70,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),X3) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_71,plain,(
    ! [X883,X884,X885,X886,X887,X888,X889,X890] : k6_enumset1(X883,X884,X885,X886,X887,X888,X889,X890) = k2_xboole_0(k5_enumset1(X883,X884,X885,X886,X887,X888,X889),k1_tarski(X890)) ),
    inference(variable_rename,[status(thm)],[t68_enumset1])).

fof(c_0_72,plain,(
    ! [X891] : k2_tarski(X891,X891) = k1_tarski(X891) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_73,plain,(
    ! [X698,X699,X700,X701,X702,X703,X704,X705,X706] : k7_enumset1(X698,X699,X700,X701,X702,X703,X704,X705,X706) = k2_xboole_0(k6_enumset1(X698,X699,X700,X701,X702,X703,X704,X705),k1_tarski(X706)) ),
    inference(variable_rename,[status(thm)],[t134_enumset1])).

fof(c_0_74,plain,(
    ! [X422,X423] : k2_xboole_0(X422,X423) = k2_xboole_0(k5_xboole_0(X422,X423),k3_xboole_0(X422,X423)) ),
    inference(variable_rename,[status(thm)],[t93_xboole_1])).

cnf(c_0_75,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_59]),c_0_65])).

cnf(c_0_76,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_77,negated_conjecture,
    ( k5_xboole_0(k2_zfmisc_1(esk47_0,esk49_0),k5_xboole_0(k2_zfmisc_1(esk47_0,esk49_0),k5_xboole_0(k2_zfmisc_1(esk48_0,esk49_0),k2_zfmisc_1(k3_tarski(k6_enumset1(esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk48_0)),esk49_0)))) != k2_zfmisc_1(k5_xboole_0(esk47_0,k5_xboole_0(esk47_0,k5_xboole_0(esk48_0,k3_tarski(k6_enumset1(esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk48_0))))),esk49_0)
    | k5_xboole_0(k2_zfmisc_1(esk49_0,esk47_0),k5_xboole_0(k2_zfmisc_1(esk49_0,esk47_0),k5_xboole_0(k2_zfmisc_1(esk49_0,esk48_0),k2_zfmisc_1(esk49_0,k3_tarski(k6_enumset1(esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk48_0)))))) != k2_zfmisc_1(esk49_0,k5_xboole_0(esk47_0,k5_xboole_0(esk47_0,k5_xboole_0(esk48_0,k3_tarski(k6_enumset1(esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk48_0)))))) ),
    inference(rw,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_78,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k5_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))) = k2_zfmisc_1(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_62]),c_0_55]),c_0_55])).

cnf(c_0_79,plain,
    ( k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),X3) = k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)),k3_tarski(k6_enumset1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48])).

cnf(c_0_80,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_81,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_82,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_83,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

fof(c_0_84,plain,(
    ! [X1122,X1123] :
      ( ( k2_zfmisc_1(X1122,X1123) != k1_xboole_0
        | X1122 = k1_xboole_0
        | X1123 = k1_xboole_0 )
      & ( X1122 != k1_xboole_0
        | k2_zfmisc_1(X1122,X1123) = k1_xboole_0 )
      & ( X1123 != k1_xboole_0
        | k2_zfmisc_1(X1122,X1123) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_85,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_86,negated_conjecture,
    ( k5_xboole_0(k2_zfmisc_1(esk47_0,esk49_0),k5_xboole_0(k2_zfmisc_1(esk47_0,esk49_0),k5_xboole_0(k2_zfmisc_1(esk48_0,esk49_0),k2_zfmisc_1(k3_tarski(k6_enumset1(esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk48_0)),esk49_0)))) != k2_zfmisc_1(k5_xboole_0(esk47_0,k5_xboole_0(esk47_0,k5_xboole_0(esk48_0,k3_tarski(k6_enumset1(esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk48_0))))),esk49_0)
    | k5_xboole_0(k2_zfmisc_1(esk49_0,esk47_0),k2_zfmisc_1(esk49_0,k5_xboole_0(esk47_0,k5_xboole_0(esk48_0,k3_tarski(k6_enumset1(esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk48_0)))))) != k2_zfmisc_1(esk49_0,k5_xboole_0(esk47_0,k5_xboole_0(esk47_0,k5_xboole_0(esk48_0,k3_tarski(k6_enumset1(esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk48_0)))))) ),
    inference(rw,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_87,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k5_xboole_0(k2_zfmisc_1(X3,X2),k2_zfmisc_1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3)),X2))) = k2_zfmisc_1(k5_xboole_0(X1,k5_xboole_0(X3,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3)))),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_68]),c_0_55]),c_0_55])).

cnf(c_0_88,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_81]),c_0_29]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48])).

cnf(c_0_89,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k3_tarski(k6_enumset1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_81]),c_0_29]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48])).

cnf(c_0_90,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k3_tarski(k6_enumset1(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_45]),c_0_46]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_48])).

fof(c_0_91,plain,(
    ! [X324] : k5_xboole_0(X324,k1_xboole_0) = X324 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_92,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_93,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X1))) = k5_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_85,c_0_55])).

cnf(c_0_94,negated_conjecture,
    ( k5_xboole_0(k2_zfmisc_1(esk47_0,esk49_0),k2_zfmisc_1(k5_xboole_0(esk47_0,k5_xboole_0(esk48_0,k3_tarski(k6_enumset1(esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk48_0)))),esk49_0)) != k2_zfmisc_1(k5_xboole_0(esk47_0,k5_xboole_0(esk47_0,k5_xboole_0(esk48_0,k3_tarski(k6_enumset1(esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk48_0))))),esk49_0)
    | k5_xboole_0(k2_zfmisc_1(esk49_0,esk47_0),k2_zfmisc_1(esk49_0,k5_xboole_0(esk47_0,k5_xboole_0(esk48_0,k3_tarski(k6_enumset1(esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk48_0)))))) != k2_zfmisc_1(esk49_0,k5_xboole_0(esk47_0,k5_xboole_0(esk47_0,k5_xboole_0(esk48_0,k3_tarski(k6_enumset1(esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk48_0)))))) ),
    inference(rw,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_95,plain,
    ( k7_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_96,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))))) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[c_0_90,c_0_55])).

cnf(c_0_97,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_98,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_92])).

cnf(c_0_99,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))),k2_zfmisc_1(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))))) = k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_78])).

cnf(c_0_100,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_55])).

cnf(c_0_101,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X3))) = k5_xboole_0(X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_85]),c_0_55])).

cnf(c_0_102,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

fof(c_0_103,plain,(
    ! [X205] : k2_xboole_0(X205,k1_xboole_0) = X205 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_104,negated_conjecture,
    ( k5_xboole_0(k2_zfmisc_1(esk47_0,esk49_0),k2_zfmisc_1(k5_xboole_0(esk47_0,k5_xboole_0(esk48_0,k3_tarski(k7_enumset1(esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk48_0)))),esk49_0)) != k2_zfmisc_1(k5_xboole_0(esk47_0,k5_xboole_0(esk47_0,k5_xboole_0(esk48_0,k3_tarski(k7_enumset1(esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk48_0))))),esk49_0)
    | k5_xboole_0(k2_zfmisc_1(esk49_0,esk47_0),k2_zfmisc_1(esk49_0,k5_xboole_0(esk47_0,k5_xboole_0(esk48_0,k3_tarski(k7_enumset1(esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk48_0)))))) != k2_zfmisc_1(esk49_0,k5_xboole_0(esk47_0,k5_xboole_0(esk47_0,k5_xboole_0(esk48_0,k3_tarski(k7_enumset1(esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk48_0)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_95]),c_0_95]),c_0_95]),c_0_95])).

cnf(c_0_105,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k5_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,k5_xboole_0(X3,X2)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_96]),c_0_55]),c_0_55]),c_0_59]),c_0_97]),c_0_55]),c_0_85]),c_0_59]),c_0_98]),c_0_76]),c_0_99]),c_0_100]),c_0_76])).

cnf(c_0_106,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X1,X4)))) = k5_xboole_0(X2,k5_xboole_0(X3,X4)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_55]),c_0_55])).

cnf(c_0_107,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_102])).

cnf(c_0_108,plain,
    ( k5_xboole_0(k2_zfmisc_1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X3),k2_zfmisc_1(k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),X3)) = k5_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_87])).

cnf(c_0_109,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_110,negated_conjecture,
    ( k5_xboole_0(k2_zfmisc_1(esk47_0,esk49_0),k2_zfmisc_1(k5_xboole_0(esk47_0,k5_xboole_0(esk48_0,k3_tarski(k7_enumset1(esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk48_0)))),esk49_0)) != k2_zfmisc_1(k5_xboole_0(esk48_0,k3_tarski(k7_enumset1(esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk48_0))),esk49_0)
    | k5_xboole_0(k2_zfmisc_1(esk49_0,esk47_0),k2_zfmisc_1(esk49_0,k5_xboole_0(esk47_0,k5_xboole_0(esk48_0,k3_tarski(k7_enumset1(esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk48_0)))))) != k2_zfmisc_1(esk49_0,k5_xboole_0(esk48_0,k3_tarski(k7_enumset1(esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk48_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_75]),c_0_75])).

cnf(c_0_111,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(X1,k5_xboole_0(X3,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_105]),c_0_97])).

cnf(c_0_112,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_76]),c_0_55])).

cnf(c_0_113,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k5_xboole_0(X1,k5_xboole_0(X2,X3)))))))) = k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_93]),c_0_55]),c_0_55]),c_0_106])).

cnf(c_0_114,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k5_xboole_0(k2_zfmisc_1(X3,X2),k2_zfmisc_1(k5_xboole_0(X3,X1),X2))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_96]),c_0_55]),c_0_55]),c_0_59]),c_0_97]),c_0_55]),c_0_85]),c_0_59]),c_0_107]),c_0_76]),c_0_108]),c_0_100]),c_0_76])).

cnf(c_0_115,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_35]),c_0_36]),c_0_37]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_116,negated_conjecture,
    ( k5_xboole_0(k2_zfmisc_1(esk47_0,esk49_0),k2_zfmisc_1(k5_xboole_0(esk47_0,k5_xboole_0(esk48_0,k3_tarski(k7_enumset1(esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk48_0)))),esk49_0)) != k2_zfmisc_1(k5_xboole_0(esk48_0,k3_tarski(k7_enumset1(esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk47_0,esk48_0))),esk49_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_111]),c_0_55]),c_0_55]),c_0_76]),c_0_112]),c_0_75])])).

cnf(c_0_117,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2)) = k2_zfmisc_1(k5_xboole_0(X3,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_115]),c_0_114]),c_0_115]),c_0_115])).

cnf(c_0_118,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_117]),c_0_55]),c_0_55]),c_0_76]),c_0_112]),c_0_75])]),
    [proof]).
%------------------------------------------------------------------------------
