%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0301+2 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 0.99s
% Output     : CNFRefutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  174 (2614 expanded)
%              Number of clauses        :   99 (1105 expanded)
%              Number of leaves         :   38 ( 763 expanded)
%              Depth                    :   21
%              Number of atoms          :  485 (5097 expanded)
%              Number of equality atoms :  202 (2692 expanded)
%              Maximal formula depth    :   52 (   4 average)
%              Maximal clause size      :   76 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t70_enumset1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t68_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t68_enumset1)).

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

fof(t134_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t134_enumset1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',t3_xboole_0)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t3_xboole_1)).

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

fof(t1_zfmisc_1,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',symmetry_r1_xboole_0)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t7_boole)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t69_xboole_1)).

fof(t79_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t2_xboole_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t65_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d3_tarski)).

fof(t6_xboole_0,axiom,(
    ! [X1,X2] :
      ~ ( r2_xboole_0(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ~ r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',t6_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d1_xboole_0)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t95_xboole_1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d8_xboole_0)).

fof(t2_zfmisc_1,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',idempotence_k3_xboole_0)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',idempotence_k2_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',d10_xboole_0)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t92_xboole_1)).

fof(fc1_zfmisc_1,axiom,(
    ! [X1,X2] : ~ v1_xboole_0(k4_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_zfmisc_1)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',t1_xboole_0)).

fof(t113_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(c_0_38,plain,(
    ! [X1055,X1056] : k3_tarski(k2_tarski(X1055,X1056)) = k2_xboole_0(X1055,X1056) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_39,plain,(
    ! [X892,X893] : k1_enumset1(X892,X892,X893) = k2_tarski(X892,X893) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_40,plain,(
    ! [X981,X982,X983,X984,X985,X986] :
      ( ( ~ r2_hidden(X983,X982)
        | r1_tarski(X983,X981)
        | X982 != k1_zfmisc_1(X981) )
      & ( ~ r1_tarski(X984,X981)
        | r2_hidden(X984,X982)
        | X982 != k1_zfmisc_1(X981) )
      & ( ~ r2_hidden(esk21_2(X985,X986),X986)
        | ~ r1_tarski(esk21_2(X985,X986),X985)
        | X986 = k1_zfmisc_1(X985) )
      & ( r2_hidden(esk21_2(X985,X986),X986)
        | r1_tarski(esk21_2(X985,X986),X985)
        | X986 = k1_zfmisc_1(X985) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_41,plain,(
    ! [X883,X884,X885,X886,X887,X888,X889,X890] : k6_enumset1(X883,X884,X885,X886,X887,X888,X889,X890) = k2_xboole_0(k5_enumset1(X883,X884,X885,X886,X887,X888,X889),k1_tarski(X890)) ),
    inference(variable_rename,[status(thm)],[t68_enumset1])).

fof(c_0_42,plain,(
    ! [X891] : k2_tarski(X891,X891) = k1_tarski(X891) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_43,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_45,plain,(
    ! [X894,X895,X896] : k2_enumset1(X894,X894,X895,X896) = k1_enumset1(X894,X895,X896) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_46,plain,(
    ! [X897,X898,X899,X900] : k3_enumset1(X897,X897,X898,X899,X900) = k2_enumset1(X897,X898,X899,X900) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_47,plain,(
    ! [X901,X902,X903,X904,X905] : k4_enumset1(X901,X901,X902,X903,X904,X905) = k3_enumset1(X901,X902,X903,X904,X905) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_48,plain,(
    ! [X906,X907,X908,X909,X910,X911] : k5_enumset1(X906,X906,X907,X908,X909,X910,X911) = k4_enumset1(X906,X907,X908,X909,X910,X911) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_49,plain,(
    ! [X912,X913,X914,X915,X916,X917,X918] : k6_enumset1(X912,X912,X913,X914,X915,X916,X917,X918) = k5_enumset1(X912,X913,X914,X915,X916,X917,X918) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_50,plain,(
    ! [X698,X699,X700,X701,X702,X703,X704,X705,X706] : k7_enumset1(X698,X699,X700,X701,X702,X703,X704,X705,X706) = k2_xboole_0(k6_enumset1(X698,X699,X700,X701,X702,X703,X704,X705),k1_tarski(X706)) ),
    inference(variable_rename,[status(thm)],[t134_enumset1])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_52,plain,(
    ! [X84,X85,X87,X88,X89] :
      ( ( r2_hidden(esk10_2(X84,X85),X84)
        | r1_xboole_0(X84,X85) )
      & ( r2_hidden(esk10_2(X84,X85),X85)
        | r1_xboole_0(X84,X85) )
      & ( ~ r2_hidden(X89,X87)
        | ~ r2_hidden(X89,X88)
        | ~ r1_xboole_0(X87,X88) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_53,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_54,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_56,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_61,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_62,plain,(
    ! [X267] :
      ( ~ r1_tarski(X267,k1_xboole_0)
      | X267 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_64,plain,
    ( r2_hidden(esk10_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_65,plain,(
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

cnf(c_0_66,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[t1_zfmisc_1])).

cnf(c_0_67,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54]),c_0_44]),c_0_55]),c_0_56]),c_0_56]),c_0_57]),c_0_57]),c_0_58]),c_0_58]),c_0_59]),c_0_59]),c_0_60]),c_0_60]),c_0_60]),c_0_60]),c_0_60]),c_0_60]),c_0_60]),c_0_60])).

cnf(c_0_68,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k3_tarski(k6_enumset1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_54]),c_0_44]),c_0_55]),c_0_56]),c_0_56]),c_0_57]),c_0_57]),c_0_58]),c_0_58]),c_0_59]),c_0_59]),c_0_60]),c_0_60])).

cnf(c_0_69,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_70,plain,
    ( r1_xboole_0(X1,k1_zfmisc_1(X2))
    | r1_tarski(esk10_2(X1,k1_zfmisc_1(X2)),X2) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k7_enumset1(X4,X5,X6,X7,X8,X9,X10,X11,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_72,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_54]),c_0_44]),c_0_56]),c_0_57]),c_0_58]),c_0_59]),c_0_60])).

cnf(c_0_73,plain,
    ( k7_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[c_0_67,c_0_68])).

fof(c_0_74,plain,(
    ! [X72,X73] :
      ( ~ r1_xboole_0(X72,X73)
      | r1_xboole_0(X73,X72) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_75,plain,
    ( r2_hidden(esk10_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_76,plain,
    ( esk10_2(X1,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | r1_xboole_0(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

fof(c_0_77,plain,(
    ! [X381,X382] :
      ( ~ r2_hidden(X381,X382)
      | ~ v1_xboole_0(X382) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,k7_enumset1(X2,X3,X4,X5,X6,X7,X8,X9,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_71])])).

cnf(c_0_79,plain,
    ( k7_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_72,c_0_73])).

fof(c_0_80,plain,(
    ! [X347,X348] :
      ( v1_xboole_0(X348)
      | ~ r1_tarski(X348,X347)
      | ~ r1_xboole_0(X348,X347) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

cnf(c_0_81,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_82,plain,
    ( r1_xboole_0(X1,k1_zfmisc_1(k1_xboole_0))
    | r2_hidden(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_83,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_84,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_85,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_86,plain,
    ( r1_xboole_0(k1_zfmisc_1(k1_xboole_0),X1)
    | r2_hidden(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_87,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

fof(c_0_88,plain,(
    ! [X1252,X1253] :
      ( ~ r1_tarski(X1252,X1253)
      | r1_tarski(k1_zfmisc_1(X1252),k1_zfmisc_1(X1253)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).

fof(c_0_89,plain,(
    ! [X239] : r1_tarski(k1_xboole_0,X239) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_90,plain,(
    ! [X339] : r1_xboole_0(X339,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_91,plain,(
    ! [X27,X28,X29,X30,X31] :
      ( ( ~ r1_tarski(X27,X28)
        | ~ r2_hidden(X29,X27)
        | r2_hidden(X29,X28) )
      & ( r2_hidden(esk2_2(X30,X31),X30)
        | r1_tarski(X30,X31) )
      & ( ~ r2_hidden(esk2_2(X30,X31),X31)
        | r1_tarski(X30,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_92,plain,(
    ! [X99,X100] :
      ( ( r2_hidden(esk12_2(X99,X100),X100)
        | ~ r2_xboole_0(X99,X100) )
      & ( ~ r2_hidden(esk12_2(X99,X100),X99)
        | ~ r2_xboole_0(X99,X100) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_xboole_0])])])])])).

fof(c_0_93,plain,(
    ! [X23,X24,X25] :
      ( ( ~ v1_xboole_0(X23)
        | ~ r2_hidden(X24,X23) )
      & ( r2_hidden(esk1_1(X25),X25)
        | v1_xboole_0(X25) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_94,plain,
    ( r2_hidden(k1_xboole_0,X1)
    | ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87])).

cnf(c_0_95,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_96,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_97,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_98,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

fof(c_0_99,plain,(
    ! [X1053,X1054] :
      ( ~ r2_hidden(X1053,X1054)
      | r1_tarski(X1053,k3_tarski(X1054)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

fof(c_0_100,plain,(
    ! [X426,X427] : k3_xboole_0(X426,X427) = k5_xboole_0(k5_xboole_0(X426,X427),k2_xboole_0(X426,X427)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_101,plain,
    ( r2_hidden(esk12_2(X1,X2),X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

fof(c_0_102,plain,(
    ! [X64,X65] :
      ( ( r1_tarski(X64,X65)
        | ~ r2_xboole_0(X64,X65) )
      & ( X64 != X65
        | ~ r2_xboole_0(X64,X65) )
      & ( ~ r1_tarski(X64,X65)
        | X64 = X65
        | r2_xboole_0(X64,X65) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_103,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_104,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96])])).

cnf(c_0_105,plain,
    ( r1_xboole_0(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_83,c_0_64])).

cnf(c_0_106,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_97])).

cnf(c_0_107,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_98])).

cnf(c_0_108,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_109,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t2_zfmisc_1])).

fof(c_0_110,plain,(
    ! [X67] : k3_xboole_0(X67,X67) = X67 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_111,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

fof(c_0_112,plain,(
    ! [X66] : k2_xboole_0(X66,X66) = X66 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_113,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_101])).

cnf(c_0_114,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_115,plain,
    ( r1_tarski(esk1_1(k1_zfmisc_1(X1)),X1)
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_103])).

cnf(c_0_116,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_104])).

cnf(c_0_117,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_118,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_107,c_0_106])).

cnf(c_0_119,plain,
    ( r1_tarski(X1,k1_xboole_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

fof(c_0_120,plain,(
    ! [X104,X105] :
      ( ( r1_tarski(X104,X105)
        | X104 != X105 )
      & ( r1_tarski(X105,X104)
        | X104 != X105 )
      & ( ~ r1_tarski(X104,X105)
        | ~ r1_tarski(X105,X104)
        | X104 = X105 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_121,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_110])).

cnf(c_0_122,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_55]),c_0_56]),c_0_57])).

fof(c_0_123,plain,(
    ! [X421] : k5_xboole_0(X421,X421) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_124,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_112])).

fof(c_0_125,plain,(
    ! [X1016,X1017] : ~ v1_xboole_0(k4_tarski(X1016,X1017)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_zfmisc_1])])).

cnf(c_0_126,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_113,c_0_114])).

cnf(c_0_127,plain,
    ( r1_tarski(esk1_1(k1_zfmisc_1(X1)),X1) ),
    inference(sr,[status(thm)],[c_0_115,c_0_116])).

cnf(c_0_128,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_85,c_0_117])).

cnf(c_0_129,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_130,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_120])).

fof(c_0_131,plain,(
    ! [X74,X75,X76] :
      ( ( ~ r2_hidden(X74,X75)
        | ~ r2_hidden(X74,X76)
        | ~ r2_hidden(X74,k5_xboole_0(X75,X76)) )
      & ( r2_hidden(X74,X75)
        | r2_hidden(X74,X76)
        | ~ r2_hidden(X74,k5_xboole_0(X75,X76)) )
      & ( ~ r2_hidden(X74,X75)
        | r2_hidden(X74,X76)
        | r2_hidden(X74,k5_xboole_0(X75,X76)) )
      & ( ~ r2_hidden(X74,X76)
        | r2_hidden(X74,X75)
        | r2_hidden(X74,k5_xboole_0(X75,X76)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_132,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_121,c_0_122]),c_0_58]),c_0_59]),c_0_60])).

cnf(c_0_133,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_123])).

cnf(c_0_134,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_124,c_0_55]),c_0_56]),c_0_57]),c_0_58]),c_0_59]),c_0_60])).

fof(c_0_135,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k1_xboole_0
      <=> ( X1 = k1_xboole_0
          | X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t113_zfmisc_1])).

cnf(c_0_136,plain,
    ( ~ v1_xboole_0(k4_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_125])).

cnf(c_0_137,plain,
    ( esk1_1(k1_zfmisc_1(X1)) = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_138,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_128,c_0_129])).

cnf(c_0_139,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_130])).

cnf(c_0_140,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_131])).

cnf(c_0_141,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_132,c_0_133]),c_0_134])).

fof(c_0_142,plain,(
    ! [X988,X989,X990,X991,X994,X995,X996,X997,X998,X999,X1001,X1002] :
      ( ( r2_hidden(esk22_4(X988,X989,X990,X991),X988)
        | ~ r2_hidden(X991,X990)
        | X990 != k2_zfmisc_1(X988,X989) )
      & ( r2_hidden(esk23_4(X988,X989,X990,X991),X989)
        | ~ r2_hidden(X991,X990)
        | X990 != k2_zfmisc_1(X988,X989) )
      & ( X991 = k4_tarski(esk22_4(X988,X989,X990,X991),esk23_4(X988,X989,X990,X991))
        | ~ r2_hidden(X991,X990)
        | X990 != k2_zfmisc_1(X988,X989) )
      & ( ~ r2_hidden(X995,X988)
        | ~ r2_hidden(X996,X989)
        | X994 != k4_tarski(X995,X996)
        | r2_hidden(X994,X990)
        | X990 != k2_zfmisc_1(X988,X989) )
      & ( ~ r2_hidden(esk24_3(X997,X998,X999),X999)
        | ~ r2_hidden(X1001,X997)
        | ~ r2_hidden(X1002,X998)
        | esk24_3(X997,X998,X999) != k4_tarski(X1001,X1002)
        | X999 = k2_zfmisc_1(X997,X998) )
      & ( r2_hidden(esk25_3(X997,X998,X999),X997)
        | r2_hidden(esk24_3(X997,X998,X999),X999)
        | X999 = k2_zfmisc_1(X997,X998) )
      & ( r2_hidden(esk26_3(X997,X998,X999),X998)
        | r2_hidden(esk24_3(X997,X998,X999),X999)
        | X999 = k2_zfmisc_1(X997,X998) )
      & ( esk24_3(X997,X998,X999) = k4_tarski(esk25_3(X997,X998,X999),esk26_3(X997,X998,X999))
        | r2_hidden(esk24_3(X997,X998,X999),X999)
        | X999 = k2_zfmisc_1(X997,X998) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

fof(c_0_143,plain,(
    ! [X1057,X1058,X1059,X1060] :
      ( ( r2_hidden(X1057,X1059)
        | ~ r2_hidden(k4_tarski(X1057,X1058),k2_zfmisc_1(X1059,X1060)) )
      & ( r2_hidden(X1058,X1060)
        | ~ r2_hidden(k4_tarski(X1057,X1058),k2_zfmisc_1(X1059,X1060)) )
      & ( ~ r2_hidden(X1057,X1059)
        | ~ r2_hidden(X1058,X1060)
        | r2_hidden(k4_tarski(X1057,X1058),k2_zfmisc_1(X1059,X1060)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

fof(c_0_144,negated_conjecture,
    ( ( esk39_0 != k1_xboole_0
      | k2_zfmisc_1(esk39_0,esk40_0) != k1_xboole_0 )
    & ( esk40_0 != k1_xboole_0
      | k2_zfmisc_1(esk39_0,esk40_0) != k1_xboole_0 )
    & ( k2_zfmisc_1(esk39_0,esk40_0) = k1_xboole_0
      | esk39_0 = k1_xboole_0
      | esk40_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_135])])])])).

cnf(c_0_145,plain,
    ( ~ r1_tarski(k4_tarski(X1,X2),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_136,c_0_106])).

cnf(c_0_146,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_137]),c_0_116])).

cnf(c_0_147,plain,
    ( v1_xboole_0(X1)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_138,c_0_139])).

cnf(c_0_148,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_140,c_0_141])).

fof(c_0_149,plain,(
    ! [X1005,X1006,X1007,X1009,X1010,X1011,X1012,X1014] :
      ( ( r2_hidden(X1007,esk27_3(X1005,X1006,X1007))
        | ~ r2_hidden(X1007,X1006)
        | X1006 != k3_tarski(X1005) )
      & ( r2_hidden(esk27_3(X1005,X1006,X1007),X1005)
        | ~ r2_hidden(X1007,X1006)
        | X1006 != k3_tarski(X1005) )
      & ( ~ r2_hidden(X1009,X1010)
        | ~ r2_hidden(X1010,X1005)
        | r2_hidden(X1009,X1006)
        | X1006 != k3_tarski(X1005) )
      & ( ~ r2_hidden(esk28_2(X1011,X1012),X1012)
        | ~ r2_hidden(esk28_2(X1011,X1012),X1014)
        | ~ r2_hidden(X1014,X1011)
        | X1012 = k3_tarski(X1011) )
      & ( r2_hidden(esk28_2(X1011,X1012),esk29_2(X1011,X1012))
        | r2_hidden(esk28_2(X1011,X1012),X1012)
        | X1012 = k3_tarski(X1011) )
      & ( r2_hidden(esk29_2(X1011,X1012),X1011)
        | r2_hidden(esk28_2(X1011,X1012),X1012)
        | X1012 = k3_tarski(X1011) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_150,plain,
    ( r2_hidden(esk22_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_142])).

cnf(c_0_151,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_143])).

cnf(c_0_152,negated_conjecture,
    ( k2_zfmisc_1(esk39_0,esk40_0) = k1_xboole_0
    | esk39_0 = k1_xboole_0
    | esk40_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_144])).

cnf(c_0_153,plain,
    ( ~ r2_hidden(k4_tarski(X1,X2),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_145,c_0_129])).

cnf(c_0_154,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_147]),c_0_148])).

cnf(c_0_155,plain,
    ( r2_hidden(esk29_2(X1,X2),X1)
    | r2_hidden(esk28_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_149])).

cnf(c_0_156,plain,
    ( r2_hidden(esk22_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_150])).

cnf(c_0_157,negated_conjecture,
    ( esk40_0 = k1_xboole_0
    | esk39_0 = k1_xboole_0
    | ~ r2_hidden(X1,esk40_0)
    | ~ r2_hidden(X2,esk39_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_152]),c_0_153])).

cnf(c_0_158,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk28_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154,c_0_155]),c_0_109])).

cnf(c_0_159,plain,
    ( r2_hidden(esk23_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_142])).

cnf(c_0_160,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k2_zfmisc_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_156])).

cnf(c_0_161,negated_conjecture,
    ( esk39_0 = k1_xboole_0
    | esk40_0 = k1_xboole_0
    | ~ r2_hidden(X1,esk39_0) ),
    inference(spm,[status(thm)],[c_0_157,c_0_158])).

cnf(c_0_162,plain,
    ( r2_hidden(esk23_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_159])).

cnf(c_0_163,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_160,c_0_158])).

cnf(c_0_164,negated_conjecture,
    ( esk40_0 != k1_xboole_0
    | k2_zfmisc_1(esk39_0,esk40_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_144])).

cnf(c_0_165,negated_conjecture,
    ( esk40_0 = k1_xboole_0
    | esk39_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_161,c_0_158])).

cnf(c_0_166,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_154,c_0_162])).

cnf(c_0_167,negated_conjecture,
    ( esk39_0 != k1_xboole_0
    | k2_zfmisc_1(esk39_0,esk40_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_144])).

cnf(c_0_168,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_163,c_0_106])).

cnf(c_0_169,negated_conjecture,
    ( esk39_0 = k1_xboole_0
    | k2_zfmisc_1(esk39_0,k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_164,c_0_165])).

cnf(c_0_170,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_166,c_0_158])).

cnf(c_0_171,negated_conjecture,
    ( ~ r1_tarski(esk39_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_167,c_0_168]),c_0_69])).

cnf(c_0_172,negated_conjecture,
    ( esk39_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_169,c_0_170])])).

cnf(c_0_173,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_171,c_0_172]),c_0_96])]),
    [proof]).
%------------------------------------------------------------------------------
