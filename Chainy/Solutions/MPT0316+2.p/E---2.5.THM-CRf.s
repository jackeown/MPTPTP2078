%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0316+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:42 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 508 expanded)
%              Number of clauses        :   35 ( 191 expanded)
%              Number of leaves         :   13 ( 156 expanded)
%              Depth                    :    9
%              Number of atoms          :  203 ( 918 expanded)
%              Number of equality atoms :  135 ( 717 expanded)
%              Maximal formula depth    :   52 (   5 average)
%              Maximal clause size      :   76 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t128_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))
    <=> ( X1 = X3
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t70_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t69_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t75_enumset1)).

fof(t68_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t68_enumset1)).

fof(t134_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t134_enumset1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(d7_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( X10 = k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)
    <=> ! [X11] :
          ( r2_hidden(X11,X10)
        <=> ~ ( X11 != X1
              & X11 != X2
              & X11 != X3
              & X11 != X4
              & X11 != X5
              & X11 != X6
              & X11 != X7
              & X11 != X8
              & X11 != X9 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',d7_enumset1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))
      <=> ( X1 = X3
          & r2_hidden(X2,X4) ) ) ),
    inference(assume_negation,[status(cth)],[t128_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X1078,X1079] : k3_tarski(k2_tarski(X1078,X1079)) = k2_xboole_0(X1078,X1079) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X892,X893] : k1_enumset1(X892,X892,X893) = k2_tarski(X892,X893) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,negated_conjecture,
    ( ( ~ r2_hidden(k4_tarski(esk47_0,esk48_0),k2_zfmisc_1(k1_tarski(esk49_0),esk50_0))
      | esk47_0 != esk49_0
      | ~ r2_hidden(esk48_0,esk50_0) )
    & ( esk47_0 = esk49_0
      | r2_hidden(k4_tarski(esk47_0,esk48_0),k2_zfmisc_1(k1_tarski(esk49_0),esk50_0)) )
    & ( r2_hidden(esk48_0,esk50_0)
      | r2_hidden(k4_tarski(esk47_0,esk48_0),k2_zfmisc_1(k1_tarski(esk49_0),esk50_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).

fof(c_0_17,plain,(
    ! [X891] : k2_tarski(X891,X891) = k1_tarski(X891) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_18,plain,(
    ! [X894,X895,X896] : k2_enumset1(X894,X894,X895,X896) = k1_enumset1(X894,X895,X896) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_19,plain,(
    ! [X897,X898,X899,X900] : k3_enumset1(X897,X897,X898,X899,X900) = k2_enumset1(X897,X898,X899,X900) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_20,plain,(
    ! [X901,X902,X903,X904,X905] : k4_enumset1(X901,X901,X902,X903,X904,X905) = k3_enumset1(X901,X902,X903,X904,X905) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_21,plain,(
    ! [X906,X907,X908,X909,X910,X911] : k5_enumset1(X906,X906,X907,X908,X909,X910,X911) = k4_enumset1(X906,X907,X908,X909,X910,X911) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_22,plain,(
    ! [X912,X913,X914,X915,X916,X917,X918] : k6_enumset1(X912,X912,X913,X914,X915,X916,X917,X918) = k5_enumset1(X912,X913,X914,X915,X916,X917,X918) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_23,plain,(
    ! [X883,X884,X885,X886,X887,X888,X889,X890] : k6_enumset1(X883,X884,X885,X886,X887,X888,X889,X890) = k2_xboole_0(k5_enumset1(X883,X884,X885,X886,X887,X888,X889),k1_tarski(X890)) ),
    inference(variable_rename,[status(thm)],[t68_enumset1])).

cnf(c_0_24,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_26,plain,(
    ! [X698,X699,X700,X701,X702,X703,X704,X705,X706] : k7_enumset1(X698,X699,X700,X701,X702,X703,X704,X705,X706) = k2_xboole_0(k6_enumset1(X698,X699,X700,X701,X702,X703,X704,X705),k1_tarski(X706)) ),
    inference(variable_rename,[status(thm)],[t134_enumset1])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk48_0,esk50_0)
    | r2_hidden(k4_tarski(esk47_0,esk48_0),k2_zfmisc_1(k1_tarski(esk49_0),esk50_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_34,plain,(
    ! [X1080,X1081,X1082,X1083] :
      ( ( r2_hidden(X1080,X1082)
        | ~ r2_hidden(k4_tarski(X1080,X1081),k2_zfmisc_1(X1082,X1083)) )
      & ( r2_hidden(X1081,X1083)
        | ~ r2_hidden(k4_tarski(X1080,X1081),k2_zfmisc_1(X1082,X1083)) )
      & ( ~ r2_hidden(X1080,X1082)
        | ~ r2_hidden(X1081,X1083)
        | r2_hidden(k4_tarski(X1080,X1081),k2_zfmisc_1(X1082,X1083)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_35,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_37,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk47_0,esk48_0),k2_zfmisc_1(k1_tarski(esk49_0),esk50_0))
    | esk47_0 != esk49_0
    | ~ r2_hidden(esk48_0,esk50_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk48_0,esk50_0)
    | r2_hidden(k4_tarski(esk47_0,esk48_0),k2_zfmisc_1(k6_enumset1(esk49_0,esk49_0,esk49_0,esk49_0,esk49_0,esk49_0,esk49_0,esk49_0),esk50_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_25]),c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( esk47_0 = esk49_0
    | r2_hidden(k4_tarski(esk47_0,esk48_0),k2_zfmisc_1(k1_tarski(esk49_0),esk50_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_42,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_28]),c_0_25]),c_0_36]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_33])).

cnf(c_0_43,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k3_tarski(k6_enumset1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_28]),c_0_25]),c_0_36]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( esk49_0 != esk47_0
    | ~ r2_hidden(esk48_0,esk50_0)
    | ~ r2_hidden(k4_tarski(esk47_0,esk48_0),k2_zfmisc_1(k6_enumset1(esk49_0,esk49_0,esk49_0,esk49_0,esk49_0,esk49_0,esk49_0,esk49_0),esk50_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_28]),c_0_25]),c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk48_0,esk50_0) ),
    inference(csr,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_46,plain,(
    ! [X470,X471,X472,X473,X474,X475,X476,X477,X478,X479,X480,X481,X482,X483,X484,X485,X486,X487,X488,X489,X490,X491] :
      ( ( ~ r2_hidden(X480,X479)
        | X480 = X470
        | X480 = X471
        | X480 = X472
        | X480 = X473
        | X480 = X474
        | X480 = X475
        | X480 = X476
        | X480 = X477
        | X480 = X478
        | X479 != k7_enumset1(X470,X471,X472,X473,X474,X475,X476,X477,X478) )
      & ( X481 != X470
        | r2_hidden(X481,X479)
        | X479 != k7_enumset1(X470,X471,X472,X473,X474,X475,X476,X477,X478) )
      & ( X481 != X471
        | r2_hidden(X481,X479)
        | X479 != k7_enumset1(X470,X471,X472,X473,X474,X475,X476,X477,X478) )
      & ( X481 != X472
        | r2_hidden(X481,X479)
        | X479 != k7_enumset1(X470,X471,X472,X473,X474,X475,X476,X477,X478) )
      & ( X481 != X473
        | r2_hidden(X481,X479)
        | X479 != k7_enumset1(X470,X471,X472,X473,X474,X475,X476,X477,X478) )
      & ( X481 != X474
        | r2_hidden(X481,X479)
        | X479 != k7_enumset1(X470,X471,X472,X473,X474,X475,X476,X477,X478) )
      & ( X481 != X475
        | r2_hidden(X481,X479)
        | X479 != k7_enumset1(X470,X471,X472,X473,X474,X475,X476,X477,X478) )
      & ( X481 != X476
        | r2_hidden(X481,X479)
        | X479 != k7_enumset1(X470,X471,X472,X473,X474,X475,X476,X477,X478) )
      & ( X481 != X477
        | r2_hidden(X481,X479)
        | X479 != k7_enumset1(X470,X471,X472,X473,X474,X475,X476,X477,X478) )
      & ( X481 != X478
        | r2_hidden(X481,X479)
        | X479 != k7_enumset1(X470,X471,X472,X473,X474,X475,X476,X477,X478) )
      & ( esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) != X482
        | ~ r2_hidden(esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491),X491)
        | X491 = k7_enumset1(X482,X483,X484,X485,X486,X487,X488,X489,X490) )
      & ( esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) != X483
        | ~ r2_hidden(esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491),X491)
        | X491 = k7_enumset1(X482,X483,X484,X485,X486,X487,X488,X489,X490) )
      & ( esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) != X484
        | ~ r2_hidden(esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491),X491)
        | X491 = k7_enumset1(X482,X483,X484,X485,X486,X487,X488,X489,X490) )
      & ( esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) != X485
        | ~ r2_hidden(esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491),X491)
        | X491 = k7_enumset1(X482,X483,X484,X485,X486,X487,X488,X489,X490) )
      & ( esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) != X486
        | ~ r2_hidden(esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491),X491)
        | X491 = k7_enumset1(X482,X483,X484,X485,X486,X487,X488,X489,X490) )
      & ( esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) != X487
        | ~ r2_hidden(esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491),X491)
        | X491 = k7_enumset1(X482,X483,X484,X485,X486,X487,X488,X489,X490) )
      & ( esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) != X488
        | ~ r2_hidden(esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491),X491)
        | X491 = k7_enumset1(X482,X483,X484,X485,X486,X487,X488,X489,X490) )
      & ( esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) != X489
        | ~ r2_hidden(esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491),X491)
        | X491 = k7_enumset1(X482,X483,X484,X485,X486,X487,X488,X489,X490) )
      & ( esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) != X490
        | ~ r2_hidden(esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491),X491)
        | X491 = k7_enumset1(X482,X483,X484,X485,X486,X487,X488,X489,X490) )
      & ( r2_hidden(esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491),X491)
        | esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) = X482
        | esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) = X483
        | esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) = X484
        | esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) = X485
        | esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) = X486
        | esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) = X487
        | esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) = X488
        | esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) = X489
        | esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) = X490
        | X491 = k7_enumset1(X482,X483,X484,X485,X486,X487,X488,X489,X490) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_enumset1])])])])])])).

cnf(c_0_47,negated_conjecture,
    ( esk49_0 = esk47_0
    | r2_hidden(k4_tarski(esk47_0,esk48_0),k2_zfmisc_1(k6_enumset1(esk49_0,esk49_0,esk49_0,esk49_0,esk49_0,esk49_0,esk49_0,esk49_0),esk50_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_28]),c_0_25]),c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_48,plain,
    ( k7_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( esk47_0 != esk49_0
    | ~ r2_hidden(k4_tarski(esk47_0,esk48_0),k2_zfmisc_1(k6_enumset1(esk49_0,esk49_0,esk49_0,esk49_0,esk49_0,esk49_0,esk49_0,esk49_0),esk50_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45])])).

cnf(c_0_50,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | X1 = X7
    | X1 = X8
    | X1 = X9
    | X1 = X10
    | X1 = X11
    | ~ r2_hidden(X1,X2)
    | X2 != k7_enumset1(X3,X4,X5,X6,X7,X8,X9,X10,X11) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_52,negated_conjecture,
    ( esk47_0 = esk49_0
    | r2_hidden(k4_tarski(esk47_0,esk48_0),k2_zfmisc_1(k7_enumset1(esk49_0,esk49_0,esk49_0,esk49_0,esk49_0,esk49_0,esk49_0,esk49_0,esk49_0),esk50_0)) ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( esk47_0 != esk49_0
    | ~ r2_hidden(k4_tarski(esk47_0,esk48_0),k2_zfmisc_1(k7_enumset1(esk49_0,esk49_0,esk49_0,esk49_0,esk49_0,esk49_0,esk49_0,esk49_0,esk49_0),esk50_0)) ),
    inference(rw,[status(thm)],[c_0_49,c_0_48])).

cnf(c_0_54,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_55,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | X1 = X7
    | X1 = X8
    | X1 = X9
    | X1 = X10
    | ~ r2_hidden(X1,k7_enumset1(X10,X9,X8,X7,X6,X5,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( esk47_0 = esk49_0
    | r2_hidden(esk47_0,k7_enumset1(esk49_0,esk49_0,esk49_0,esk49_0,esk49_0,esk49_0,esk49_0,esk49_0,esk49_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k7_enumset1(X2,X4,X5,X6,X7,X8,X9,X10,X11) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,negated_conjecture,
    ( esk47_0 != esk49_0
    | ~ r2_hidden(esk47_0,k7_enumset1(esk49_0,esk49_0,esk49_0,esk49_0,esk49_0,esk49_0,esk49_0,esk49_0,esk49_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_45])])).

cnf(c_0_59,negated_conjecture,
    ( esk47_0 = esk49_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_57])])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59]),c_0_59]),c_0_60])]),
    [proof]).
%------------------------------------------------------------------------------
