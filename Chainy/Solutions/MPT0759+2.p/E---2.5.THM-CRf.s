%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0759+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:52 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 814 expanded)
%              Number of clauses        :   40 ( 293 expanded)
%              Number of leaves         :   21 ( 260 expanded)
%              Depth                    :    9
%              Number of atoms          :  101 ( 832 expanded)
%              Number of equality atoms :   80 ( 811 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT006+2.ax',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t70_enumset1)).

fof(t52_ordinal1,conjecture,(
    ! [X1] : k6_subset_1(k1_ordinal1(X1),k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t69_enumset1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',l51_zfmisc_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t100_xboole_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT005+2.ax',redefinition_k6_subset_1)).

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

fof(t125_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t125_enumset1)).

fof(t61_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t61_enumset1)).

fof(t67_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t67_enumset1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t40_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',commutativity_k2_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',d10_xboole_0)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',t65_zfmisc_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(c_0_21,plain,(
    ! [X1971,X1972] : k1_setfam_1(k2_tarski(X1971,X1972)) = k3_xboole_0(X1971,X1972) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_22,plain,(
    ! [X892,X893] : k1_enumset1(X892,X892,X893) = k2_tarski(X892,X893) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1] : k6_subset_1(k1_ordinal1(X1),k1_tarski(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t52_ordinal1])).

fof(c_0_24,plain,(
    ! [X3174] : k1_ordinal1(X3174) = k2_xboole_0(X3174,k1_tarski(X3174)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_25,plain,(
    ! [X891] : k2_tarski(X891,X891) = k1_tarski(X891) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_26,plain,(
    ! [X1087,X1088] : k3_tarski(k2_tarski(X1087,X1088)) = k2_xboole_0(X1087,X1088) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_27,plain,(
    ! [X127,X128] : k4_xboole_0(X127,X128) = k5_xboole_0(X127,k3_xboole_0(X127,X128)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_28,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,negated_conjecture,(
    k6_subset_1(k1_ordinal1(esk255_0),k1_tarski(esk255_0)) != esk255_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

fof(c_0_31,plain,(
    ! [X1657,X1658] : k6_subset_1(X1657,X1658) = k4_xboole_0(X1657,X1658) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_32,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_37,plain,(
    ! [X894,X895,X896] : k2_enumset1(X894,X894,X895,X896) = k1_enumset1(X894,X895,X896) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_38,plain,(
    ! [X897,X898,X899,X900] : k3_enumset1(X897,X897,X898,X899,X900) = k2_enumset1(X897,X898,X899,X900) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_39,plain,(
    ! [X901,X902,X903,X904,X905] : k4_enumset1(X901,X901,X902,X903,X904,X905) = k3_enumset1(X901,X902,X903,X904,X905) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_40,plain,(
    ! [X906,X907,X908,X909,X910,X911] : k5_enumset1(X906,X906,X907,X908,X909,X910,X911) = k4_enumset1(X906,X907,X908,X909,X910,X911) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_41,plain,(
    ! [X912,X913,X914,X915,X916,X917,X918] : k6_enumset1(X912,X912,X913,X914,X915,X916,X917,X918) = k5_enumset1(X912,X913,X914,X915,X916,X917,X918) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_42,plain,(
    ! [X631,X632,X633,X634] : k2_enumset1(X631,X632,X633,X634) = k2_enumset1(X634,X633,X632,X631) ),
    inference(variable_rename,[status(thm)],[t125_enumset1])).

fof(c_0_43,plain,(
    ! [X828,X829,X830,X831,X832,X833,X834] : k5_enumset1(X828,X829,X830,X831,X832,X833,X834) = k2_xboole_0(k4_enumset1(X828,X829,X830,X831,X832,X833),k1_tarski(X834)) ),
    inference(variable_rename,[status(thm)],[t61_enumset1])).

fof(c_0_44,plain,(
    ! [X875,X876,X877,X878,X879,X880,X881,X882] : k6_enumset1(X875,X876,X877,X878,X879,X880,X881,X882) = k2_xboole_0(k4_enumset1(X875,X876,X877,X878,X879,X880),k2_tarski(X881,X882)) ),
    inference(variable_rename,[status(thm)],[t67_enumset1])).

cnf(c_0_45,negated_conjecture,
    ( k6_subset_1(k1_ordinal1(esk255_0),k1_tarski(esk255_0)) != esk255_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_46,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_47,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_48,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_34,c_0_29])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_50,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_54,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_55,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_56,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_57,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_58,plain,(
    ! [X268,X269] : k4_xboole_0(k2_xboole_0(X268,X269),X269) = k4_xboole_0(X268,X269) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_59,plain,(
    ! [X441,X442] : k2_tarski(X441,X442) = k2_tarski(X442,X441) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_60,negated_conjecture,
    ( k5_xboole_0(k3_tarski(k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0))),k1_setfam_1(k6_enumset1(k3_tarski(k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0))),k3_tarski(k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0))),k3_tarski(k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0))),k3_tarski(k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0))),k3_tarski(k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0))),k3_tarski(k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0))),k3_tarski(k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0))),k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0)))) != esk255_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_33]),c_0_46]),c_0_47]),c_0_29]),c_0_29]),c_0_48]),c_0_49]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54])).

cnf(c_0_61,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X4,X4,X4,X4,X4,X3,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_54]),c_0_54])).

cnf(c_0_62,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_33]),c_0_29]),c_0_48]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54])).

cnf(c_0_63,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_29]),c_0_48]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54])).

cnf(c_0_64,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_65,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_66,plain,(
    ! [X104,X105] :
      ( ( r1_tarski(X104,X105)
        | X104 != X105 )
      & ( r1_tarski(X105,X104)
        | X104 != X105 )
      & ( ~ r1_tarski(X104,X105)
        | ~ r1_tarski(X105,X104)
        | X104 = X105 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_67,negated_conjecture,
    ( k5_xboole_0(k3_tarski(k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0))),k1_setfam_1(k6_enumset1(k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0),k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0),k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0),k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0),k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0),k3_tarski(k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0))),k3_tarski(k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0))),k3_tarski(k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0)))))) != esk255_0 ),
    inference(rw,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_68,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X7) = k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_69,plain,
    ( k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_setfam_1(k6_enumset1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X2))) = k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_48]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54])).

cnf(c_0_70,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_29]),c_0_29]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_54]),c_0_54])).

fof(c_0_71,plain,(
    ! [X1396,X1397] :
      ( ( k4_xboole_0(X1396,k1_tarski(X1397)) != X1396
        | ~ r2_hidden(X1397,X1396) )
      & ( r2_hidden(X1397,X1396)
        | k4_xboole_0(X1396,k1_tarski(X1397)) = X1396 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_72,plain,(
    ! [X3327,X3328] :
      ( ~ r2_hidden(X3327,X3328)
      | ~ r1_tarski(X3328,X3327) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( k5_xboole_0(k3_tarski(k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0))),k1_setfam_1(k6_enumset1(k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0),k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0),k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0),k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0),k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0),k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0),k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0),k3_tarski(k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0)))))) != esk255_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68]),c_0_68])).

cnf(c_0_75,plain,
    ( k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) = k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(X2,k1_tarski(X1)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_77,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_78,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( k5_xboole_0(esk255_0,k1_setfam_1(k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,k6_enumset1(esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0,esk255_0)))) != esk255_0 ),
    inference(rw,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_80,plain,
    ( k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = X2
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_33]),c_0_29]),c_0_49]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_54]),c_0_54])).

cnf(c_0_81,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81]),
    [proof]).
%------------------------------------------------------------------------------
