%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0221+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:41 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 316 expanded)
%              Number of clauses        :   37 ( 115 expanded)
%              Number of leaves         :   20 (  96 expanded)
%              Depth                    :    9
%              Number of atoms          :  212 ( 481 expanded)
%              Number of equality atoms :  119 ( 354 expanded)
%              Maximal formula depth    :   52 (   5 average)
%              Maximal clause size      :   76 (   1 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t16_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),k1_tarski(X2))
        & X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t70_enumset1)).

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

fof(t68_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t68_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t100_xboole_1)).

fof(t134_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t134_enumset1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',t4_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',t3_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d1_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t28_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',d10_xboole_0)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',idempotence_k3_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',d7_enumset1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t7_boole)).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( r1_xboole_0(k1_tarski(X1),k1_tarski(X2))
          & X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t16_zfmisc_1])).

fof(c_0_21,negated_conjecture,
    ( r1_xboole_0(k1_tarski(esk25_0),k1_tarski(esk26_0))
    & esk25_0 = esk26_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_22,plain,(
    ! [X891] : k2_tarski(X891,X891) = k1_tarski(X891) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_23,plain,(
    ! [X892,X893] : k1_enumset1(X892,X892,X893) = k2_tarski(X892,X893) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_24,plain,(
    ! [X894,X895,X896] : k2_enumset1(X894,X894,X895,X896) = k1_enumset1(X894,X895,X896) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_25,plain,(
    ! [X897,X898,X899,X900] : k3_enumset1(X897,X897,X898,X899,X900) = k2_enumset1(X897,X898,X899,X900) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_26,plain,(
    ! [X901,X902,X903,X904,X905] : k4_enumset1(X901,X901,X902,X903,X904,X905) = k3_enumset1(X901,X902,X903,X904,X905) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_27,plain,(
    ! [X906,X907,X908,X909,X910,X911] : k5_enumset1(X906,X906,X907,X908,X909,X910,X911) = k4_enumset1(X906,X907,X908,X909,X910,X911) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_28,plain,(
    ! [X912,X913,X914,X915,X916,X917,X918] : k6_enumset1(X912,X912,X913,X914,X915,X916,X917,X918) = k5_enumset1(X912,X913,X914,X915,X916,X917,X918) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_29,plain,(
    ! [X883,X884,X885,X886,X887,X888,X889,X890] : k6_enumset1(X883,X884,X885,X886,X887,X888,X889,X890) = k2_xboole_0(k5_enumset1(X883,X884,X885,X886,X887,X888,X889),k1_tarski(X890)) ),
    inference(variable_rename,[status(thm)],[t68_enumset1])).

fof(c_0_30,plain,(
    ! [X433,X434] : k2_xboole_0(X433,X434) = k5_xboole_0(X433,k4_xboole_0(X434,X433)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_31,plain,(
    ! [X127,X128] : k4_xboole_0(X127,X128) = k5_xboole_0(X127,k3_xboole_0(X127,X128)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_32,plain,(
    ! [X698,X699,X700,X701,X702,X703,X704,X705,X706] : k7_enumset1(X698,X699,X700,X701,X702,X703,X704,X705,X706) = k2_xboole_0(k6_enumset1(X698,X699,X700,X701,X702,X703,X704,X705),k1_tarski(X706)) ),
    inference(variable_rename,[status(thm)],[t134_enumset1])).

fof(c_0_33,plain,(
    ! [X90,X91,X93,X94,X95] :
      ( ( r1_xboole_0(X90,X91)
        | r2_hidden(esk11_2(X90,X91),k3_xboole_0(X90,X91)) )
      & ( ~ r2_hidden(X95,k3_xboole_0(X93,X94))
        | ~ r1_xboole_0(X93,X94) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_34,plain,(
    ! [X84,X85,X87,X88,X89] :
      ( ( r2_hidden(esk10_2(X84,X85),X84)
        | r1_xboole_0(X84,X85) )
      & ( r2_hidden(esk10_2(X84,X85),X85)
        | r1_xboole_0(X84,X85) )
      & ( ~ r2_hidden(X89,X87)
        | ~ r2_hidden(X89,X88)
        | ~ r1_xboole_0(X87,X88) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_35,negated_conjecture,
    ( r1_xboole_0(k1_tarski(esk25_0),k1_tarski(esk26_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_37,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_38,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_47,plain,(
    ! [X23,X24,X25] :
      ( ( ~ v1_xboole_0(X23)
        | ~ r2_hidden(X24,X23) )
      & ( r2_hidden(esk1_1(X25),X25)
        | v1_xboole_0(X25) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_49,plain,
    ( r2_hidden(esk10_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_50,plain,(
    ! [X233,X234] :
      ( ~ r1_tarski(X233,X234)
      | k3_xboole_0(X233,X234) = X233 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_51,negated_conjecture,
    ( r1_xboole_0(k6_enumset1(esk25_0,esk25_0,esk25_0,esk25_0,esk25_0,esk25_0,esk25_0,esk25_0),k6_enumset1(esk26_0,esk26_0,esk26_0,esk26_0,esk26_0,esk26_0,esk26_0,esk26_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( esk25_0 = esk26_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_53,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_36]),c_0_37]),c_0_44]),c_0_45]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_42])).

cnf(c_0_54,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k5_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k3_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_36]),c_0_37]),c_0_44]),c_0_45]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42])).

fof(c_0_55,plain,(
    ! [X104,X105] :
      ( ( r1_tarski(X104,X105)
        | X104 != X105 )
      & ( r1_tarski(X105,X104)
        | X104 != X105 )
      & ( ~ r1_tarski(X104,X105)
        | ~ r1_tarski(X105,X104)
        | X104 = X105 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_56,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_57,plain,(
    ! [X67] : k3_xboole_0(X67,X67) = X67 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_58,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_59,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( r1_xboole_0(k6_enumset1(esk26_0,esk26_0,esk26_0,esk26_0,esk26_0,esk26_0,esk26_0,esk26_0),k6_enumset1(esk26_0,esk26_0,esk26_0,esk26_0,esk26_0,esk26_0,esk26_0,esk26_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52])).

cnf(c_0_61,plain,
    ( k7_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_63,plain,(
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

cnf(c_0_64,plain,
    ( v1_xboole_0(k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_56])).

cnf(c_0_65,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_66,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( r1_xboole_0(k7_enumset1(esk26_0,esk26_0,esk26_0,esk26_0,esk26_0,esk26_0,esk26_0,esk26_0,esk26_0),k7_enumset1(esk26_0,esk26_0,esk26_0,esk26_0,esk26_0,esk26_0,esk26_0,esk26_0,esk26_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61]),c_0_61])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_62])).

fof(c_0_69,plain,(
    ! [X381,X382] :
      ( ~ r2_hidden(X381,X382)
      | ~ v1_xboole_0(X382) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k7_enumset1(X4,X5,X6,X7,X8,X9,X10,X11,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_71,plain,
    ( v1_xboole_0(X1)
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( r1_xboole_0(k7_enumset1(esk26_0,esk26_0,esk26_0,esk26_0,esk26_0,esk26_0,esk26_0,esk26_0,esk26_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])])).

cnf(c_0_73,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,k7_enumset1(X2,X3,X4,X5,X6,X7,X8,X9,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_70])])).

cnf(c_0_75,negated_conjecture,
    ( v1_xboole_0(k7_enumset1(esk26_0,esk26_0,esk26_0,esk26_0,esk26_0,esk26_0,esk26_0,esk26_0,esk26_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_76,plain,
    ( ~ v1_xboole_0(k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_75,c_0_76]),
    [proof]).
%------------------------------------------------------------------------------
