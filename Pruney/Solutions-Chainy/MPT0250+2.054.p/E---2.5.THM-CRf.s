%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:40:14 EST 2020

% Result     : Theorem 9.28s
% Output     : CNFRefutation 9.28s
% Verified   : 
% Statistics : Number of formulae       :   86 (1127 expanded)
%              Number of clauses        :   45 ( 409 expanded)
%              Number of leaves         :   20 ( 358 expanded)
%              Depth                    :   13
%              Number of atoms          :  211 (1258 expanded)
%              Number of equality atoms :  140 (1178 expanded)
%              Maximal formula depth    :   52 (   4 average)
%              Maximal clause size      :   76 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)
     => r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(l75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(t131_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_enumset1)).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)
       => r2_hidden(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t45_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X108,X109] : k3_tarski(k2_tarski(X108,X109)) = k2_xboole_0(X108,X109) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_22,plain,(
    ! [X81,X82] : k1_enumset1(X81,X81,X82) = k2_tarski(X81,X82) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(esk3_0),esk4_0),esk4_0)
    & ~ r2_hidden(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_24,plain,(
    ! [X80] : k2_tarski(X80,X80) = k1_tarski(X80) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_25,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_27,plain,(
    ! [X83,X84,X85] : k2_enumset1(X83,X83,X84,X85) = k1_enumset1(X83,X84,X85) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_28,plain,(
    ! [X86,X87,X88,X89] : k3_enumset1(X86,X86,X87,X88,X89) = k2_enumset1(X86,X87,X88,X89) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_29,plain,(
    ! [X90,X91,X92,X93,X94] : k4_enumset1(X90,X90,X91,X92,X93,X94) = k3_enumset1(X90,X91,X92,X93,X94) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_30,plain,(
    ! [X95,X96,X97,X98,X99,X100] : k5_enumset1(X95,X95,X96,X97,X98,X99,X100) = k4_enumset1(X95,X96,X97,X98,X99,X100) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_31,plain,(
    ! [X101,X102,X103,X104,X105,X106,X107] : k6_enumset1(X101,X101,X102,X103,X104,X105,X106,X107) = k5_enumset1(X101,X102,X103,X104,X105,X106,X107) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_32,plain,(
    ! [X38,X39] : k2_xboole_0(X38,X39) = k5_xboole_0(X38,k4_xboole_0(X39,X38)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_33,plain,(
    ! [X26,X27] : k4_xboole_0(X26,X27) = k5_xboole_0(X26,k3_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_34,plain,(
    ! [X63,X64,X65,X66,X67,X68,X69,X70] : k6_enumset1(X63,X64,X65,X66,X67,X68,X69,X70) = k2_xboole_0(k2_enumset1(X63,X64,X65,X66),k2_enumset1(X67,X68,X69,X70)) ),
    inference(variable_rename,[status(thm)],[l75_enumset1])).

fof(c_0_35,plain,(
    ! [X71,X72,X73,X74,X75,X76,X77,X78,X79] : k7_enumset1(X71,X72,X73,X74,X75,X76,X77,X78,X79) = k2_xboole_0(k3_enumset1(X71,X72,X73,X74,X75),k2_enumset1(X76,X77,X78,X79)) ),
    inference(variable_rename,[status(thm)],[t131_enumset1])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(esk3_0),esk4_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_39,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_26]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43])).

cnf(c_0_49,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_38]),c_0_45]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_50,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_38]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43])).

cnf(c_0_51,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X7,X8,X9))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_38]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43])).

fof(c_0_52,plain,(
    ! [X14,X15] : k5_xboole_0(X14,X15) = k5_xboole_0(X15,X14) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_53,plain,(
    ! [X35,X36,X37] : k5_xboole_0(k5_xboole_0(X35,X36),X37) = k5_xboole_0(X35,k5_xboole_0(X36,X37)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))),esk4_0) ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,plain,
    ( k7_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_57,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_58,plain,(
    ! [X12,X13] : k3_xboole_0(X12,X13) = k3_xboole_0(X13,X12) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_59,plain,(
    ! [X33,X34] : r1_tarski(X33,k2_xboole_0(X33,X34)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55]),c_0_55])).

cnf(c_0_61,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_63,plain,(
    ! [X31,X32] :
      ( ~ r1_tarski(X31,X32)
      | k3_xboole_0(X31,X32) = X31 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_65,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22,X23] :
      ( ( ~ r2_hidden(X19,X18)
        | r2_hidden(X19,X16)
        | r2_hidden(X19,X17)
        | X18 != k2_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X20,X16)
        | r2_hidden(X20,X18)
        | X18 != k2_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X20,X17)
        | r2_hidden(X20,X18)
        | X18 != k2_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk1_3(X21,X22,X23),X21)
        | ~ r2_hidden(esk1_3(X21,X22,X23),X23)
        | X23 = k2_xboole_0(X21,X22) )
      & ( ~ r2_hidden(esk1_3(X21,X22,X23),X22)
        | ~ r2_hidden(esk1_3(X21,X22,X23),X23)
        | X23 = k2_xboole_0(X21,X22) )
      & ( r2_hidden(esk1_3(X21,X22,X23),X23)
        | r2_hidden(esk1_3(X21,X22,X23),X21)
        | r2_hidden(esk1_3(X21,X22,X23),X22)
        | X23 = k2_xboole_0(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk4_0,k5_xboole_0(k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(esk4_0,k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61]),c_0_56])).

cnf(c_0_67,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_62])).

cnf(c_0_68,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k3_tarski(k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67]),c_0_55])).

cnf(c_0_72,plain,
    ( k3_xboole_0(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = X1 ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

fof(c_0_73,plain,(
    ! [X40,X41,X42,X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53,X54,X55,X56,X57,X58,X59,X60,X61] :
      ( ( ~ r2_hidden(X50,X49)
        | X50 = X40
        | X50 = X41
        | X50 = X42
        | X50 = X43
        | X50 = X44
        | X50 = X45
        | X50 = X46
        | X50 = X47
        | X50 = X48
        | X49 != k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48) )
      & ( X51 != X40
        | r2_hidden(X51,X49)
        | X49 != k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48) )
      & ( X51 != X41
        | r2_hidden(X51,X49)
        | X49 != k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48) )
      & ( X51 != X42
        | r2_hidden(X51,X49)
        | X49 != k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48) )
      & ( X51 != X43
        | r2_hidden(X51,X49)
        | X49 != k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48) )
      & ( X51 != X44
        | r2_hidden(X51,X49)
        | X49 != k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48) )
      & ( X51 != X45
        | r2_hidden(X51,X49)
        | X49 != k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48) )
      & ( X51 != X46
        | r2_hidden(X51,X49)
        | X49 != k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48) )
      & ( X51 != X47
        | r2_hidden(X51,X49)
        | X49 != k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48) )
      & ( X51 != X48
        | r2_hidden(X51,X49)
        | X49 != k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48) )
      & ( esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61) != X52
        | ~ r2_hidden(esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61),X61)
        | X61 = k7_enumset1(X52,X53,X54,X55,X56,X57,X58,X59,X60) )
      & ( esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61) != X53
        | ~ r2_hidden(esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61),X61)
        | X61 = k7_enumset1(X52,X53,X54,X55,X56,X57,X58,X59,X60) )
      & ( esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61) != X54
        | ~ r2_hidden(esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61),X61)
        | X61 = k7_enumset1(X52,X53,X54,X55,X56,X57,X58,X59,X60) )
      & ( esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61) != X55
        | ~ r2_hidden(esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61),X61)
        | X61 = k7_enumset1(X52,X53,X54,X55,X56,X57,X58,X59,X60) )
      & ( esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61) != X56
        | ~ r2_hidden(esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61),X61)
        | X61 = k7_enumset1(X52,X53,X54,X55,X56,X57,X58,X59,X60) )
      & ( esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61) != X57
        | ~ r2_hidden(esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61),X61)
        | X61 = k7_enumset1(X52,X53,X54,X55,X56,X57,X58,X59,X60) )
      & ( esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61) != X58
        | ~ r2_hidden(esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61),X61)
        | X61 = k7_enumset1(X52,X53,X54,X55,X56,X57,X58,X59,X60) )
      & ( esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61) != X59
        | ~ r2_hidden(esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61),X61)
        | X61 = k7_enumset1(X52,X53,X54,X55,X56,X57,X58,X59,X60) )
      & ( esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61) != X60
        | ~ r2_hidden(esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61),X61)
        | X61 = k7_enumset1(X52,X53,X54,X55,X56,X57,X58,X59,X60) )
      & ( r2_hidden(esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61),X61)
        | esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61) = X52
        | esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61) = X53
        | esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61) = X54
        | esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61) = X55
        | esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61) = X56
        | esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61) = X57
        | esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61) = X58
        | esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61) = X59
        | esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61) = X60
        | X61 = k7_enumset1(X52,X53,X54,X55,X56,X57,X58,X59,X60) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_enumset1])])])])])])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_75,negated_conjecture,
    ( k3_xboole_0(esk4_0,k3_tarski(k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) = k3_tarski(k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_71]),c_0_62])).

cnf(c_0_76,plain,
    ( k3_xboole_0(X1,k3_tarski(k7_enumset1(X1,X1,X1,X1,X1,X1,X1,X1,X2))) = X1 ),
    inference(spm,[status(thm)],[c_0_72,c_0_55])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k7_enumset1(X4,X5,X6,X7,X8,X9,X10,X11,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,X2)
    | X2 != k3_tarski(k7_enumset1(X3,X3,X3,X3,X3,X3,X3,X3,X4))
    | ~ r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_74,c_0_55])).

cnf(c_0_79,negated_conjecture,
    ( k3_tarski(k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_80,plain,
    ( r2_hidden(X1,X2)
    | X2 != k7_enumset1(X3,X4,X5,X6,X7,X8,X9,X10,X1) ),
    inference(er,[status(thm)],[c_0_77])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(X1,X2)
    | X2 != esk4_0
    | ~ r2_hidden(X1,k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_82,plain,
    ( r2_hidden(X1,k7_enumset1(X2,X3,X4,X5,X6,X7,X8,X9,X1)) ),
    inference(er,[status(thm)],[c_0_80])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | X1 != esk4_0 ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_84,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_83]),c_0_84]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:21:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 9.28/9.48  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 9.28/9.48  # and selection function SelectNegativeLiterals.
% 9.28/9.48  #
% 9.28/9.48  # Preprocessing time       : 0.029 s
% 9.28/9.48  
% 9.28/9.48  # Proof found!
% 9.28/9.48  # SZS status Theorem
% 9.28/9.48  # SZS output start CNFRefutation
% 9.28/9.48  fof(t45_zfmisc_1, conjecture, ![X1, X2]:(r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 9.28/9.48  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 9.28/9.48  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 9.28/9.48  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 9.28/9.48  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 9.28/9.48  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 9.28/9.48  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 9.28/9.48  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 9.28/9.48  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 9.28/9.48  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 9.28/9.48  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.28/9.48  fof(l75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l75_enumset1)).
% 9.28/9.48  fof(t131_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t131_enumset1)).
% 9.28/9.48  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 9.28/9.48  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 9.28/9.48  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.28/9.48  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 9.28/9.48  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.28/9.48  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 9.28/9.48  fof(d7_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9, X10]:(X10=k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)<=>![X11]:(r2_hidden(X11,X10)<=>~(((((((((X11!=X1&X11!=X2)&X11!=X3)&X11!=X4)&X11!=X5)&X11!=X6)&X11!=X7)&X11!=X8)&X11!=X9)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_enumset1)).
% 9.28/9.48  fof(c_0_20, negated_conjecture, ~(![X1, X2]:(r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)=>r2_hidden(X1,X2))), inference(assume_negation,[status(cth)],[t45_zfmisc_1])).
% 9.28/9.48  fof(c_0_21, plain, ![X108, X109]:k3_tarski(k2_tarski(X108,X109))=k2_xboole_0(X108,X109), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 9.28/9.48  fof(c_0_22, plain, ![X81, X82]:k1_enumset1(X81,X81,X82)=k2_tarski(X81,X82), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 9.28/9.48  fof(c_0_23, negated_conjecture, (r1_tarski(k2_xboole_0(k1_tarski(esk3_0),esk4_0),esk4_0)&~r2_hidden(esk3_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 9.28/9.48  fof(c_0_24, plain, ![X80]:k2_tarski(X80,X80)=k1_tarski(X80), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 9.28/9.48  cnf(c_0_25, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 9.28/9.48  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 9.28/9.48  fof(c_0_27, plain, ![X83, X84, X85]:k2_enumset1(X83,X83,X84,X85)=k1_enumset1(X83,X84,X85), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 9.28/9.48  fof(c_0_28, plain, ![X86, X87, X88, X89]:k3_enumset1(X86,X86,X87,X88,X89)=k2_enumset1(X86,X87,X88,X89), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 9.28/9.48  fof(c_0_29, plain, ![X90, X91, X92, X93, X94]:k4_enumset1(X90,X90,X91,X92,X93,X94)=k3_enumset1(X90,X91,X92,X93,X94), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 9.28/9.48  fof(c_0_30, plain, ![X95, X96, X97, X98, X99, X100]:k5_enumset1(X95,X95,X96,X97,X98,X99,X100)=k4_enumset1(X95,X96,X97,X98,X99,X100), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 9.28/9.48  fof(c_0_31, plain, ![X101, X102, X103, X104, X105, X106, X107]:k6_enumset1(X101,X101,X102,X103,X104,X105,X106,X107)=k5_enumset1(X101,X102,X103,X104,X105,X106,X107), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 9.28/9.48  fof(c_0_32, plain, ![X38, X39]:k2_xboole_0(X38,X39)=k5_xboole_0(X38,k4_xboole_0(X39,X38)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 9.28/9.48  fof(c_0_33, plain, ![X26, X27]:k4_xboole_0(X26,X27)=k5_xboole_0(X26,k3_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 9.28/9.48  fof(c_0_34, plain, ![X63, X64, X65, X66, X67, X68, X69, X70]:k6_enumset1(X63,X64,X65,X66,X67,X68,X69,X70)=k2_xboole_0(k2_enumset1(X63,X64,X65,X66),k2_enumset1(X67,X68,X69,X70)), inference(variable_rename,[status(thm)],[l75_enumset1])).
% 9.28/9.48  fof(c_0_35, plain, ![X71, X72, X73, X74, X75, X76, X77, X78, X79]:k7_enumset1(X71,X72,X73,X74,X75,X76,X77,X78,X79)=k2_xboole_0(k3_enumset1(X71,X72,X73,X74,X75),k2_enumset1(X76,X77,X78,X79)), inference(variable_rename,[status(thm)],[t131_enumset1])).
% 9.28/9.48  cnf(c_0_36, negated_conjecture, (r1_tarski(k2_xboole_0(k1_tarski(esk3_0),esk4_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 9.28/9.48  cnf(c_0_37, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 9.28/9.48  cnf(c_0_38, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 9.28/9.48  cnf(c_0_39, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 9.28/9.48  cnf(c_0_40, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 9.28/9.48  cnf(c_0_41, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 9.28/9.48  cnf(c_0_42, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 9.28/9.48  cnf(c_0_43, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 9.28/9.48  cnf(c_0_44, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 9.28/9.48  cnf(c_0_45, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 9.28/9.48  cnf(c_0_46, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 9.28/9.48  cnf(c_0_47, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 9.28/9.48  cnf(c_0_48, negated_conjecture, (r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_26]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43])).
% 9.28/9.48  cnf(c_0_49, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_38]), c_0_45]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43])).
% 9.28/9.48  cnf(c_0_50, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_38]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43])).
% 9.28/9.48  cnf(c_0_51, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X7,X8,X9)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_38]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43])).
% 9.28/9.48  fof(c_0_52, plain, ![X14, X15]:k5_xboole_0(X14,X15)=k5_xboole_0(X15,X14), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 9.28/9.48  fof(c_0_53, plain, ![X35, X36, X37]:k5_xboole_0(k5_xboole_0(X35,X36),X37)=k5_xboole_0(X35,k5_xboole_0(X36,X37)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 9.28/9.48  cnf(c_0_54, negated_conjecture, (r1_tarski(k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))),esk4_0)), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 9.28/9.48  cnf(c_0_55, plain, (k7_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8)=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(rw,[status(thm)],[c_0_50, c_0_51])).
% 9.28/9.48  cnf(c_0_56, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 9.28/9.48  cnf(c_0_57, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 9.28/9.48  fof(c_0_58, plain, ![X12, X13]:k3_xboole_0(X12,X13)=k3_xboole_0(X13,X12), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 9.28/9.48  fof(c_0_59, plain, ![X33, X34]:r1_tarski(X33,k2_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 9.28/9.48  cnf(c_0_60, negated_conjecture, (r1_tarski(k5_xboole_0(k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55]), c_0_55])).
% 9.28/9.48  cnf(c_0_61, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X3,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 9.28/9.48  cnf(c_0_62, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 9.28/9.48  fof(c_0_63, plain, ![X31, X32]:(~r1_tarski(X31,X32)|k3_xboole_0(X31,X32)=X31), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 9.28/9.48  cnf(c_0_64, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 9.28/9.48  fof(c_0_65, plain, ![X16, X17, X18, X19, X20, X21, X22, X23]:(((~r2_hidden(X19,X18)|(r2_hidden(X19,X16)|r2_hidden(X19,X17))|X18!=k2_xboole_0(X16,X17))&((~r2_hidden(X20,X16)|r2_hidden(X20,X18)|X18!=k2_xboole_0(X16,X17))&(~r2_hidden(X20,X17)|r2_hidden(X20,X18)|X18!=k2_xboole_0(X16,X17))))&(((~r2_hidden(esk1_3(X21,X22,X23),X21)|~r2_hidden(esk1_3(X21,X22,X23),X23)|X23=k2_xboole_0(X21,X22))&(~r2_hidden(esk1_3(X21,X22,X23),X22)|~r2_hidden(esk1_3(X21,X22,X23),X23)|X23=k2_xboole_0(X21,X22)))&(r2_hidden(esk1_3(X21,X22,X23),X23)|(r2_hidden(esk1_3(X21,X22,X23),X21)|r2_hidden(esk1_3(X21,X22,X23),X22))|X23=k2_xboole_0(X21,X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 9.28/9.48  cnf(c_0_66, negated_conjecture, (r1_tarski(k5_xboole_0(esk4_0,k5_xboole_0(k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(esk4_0,k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61]), c_0_56])).
% 9.28/9.48  cnf(c_0_67, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_49, c_0_62])).
% 9.28/9.48  cnf(c_0_68, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 9.28/9.48  cnf(c_0_69, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43])).
% 9.28/9.48  cnf(c_0_70, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 9.28/9.48  cnf(c_0_71, negated_conjecture, (r1_tarski(k3_tarski(k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67]), c_0_55])).
% 9.28/9.48  cnf(c_0_72, plain, (k3_xboole_0(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))=X1), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 9.28/9.48  fof(c_0_73, plain, ![X40, X41, X42, X43, X44, X45, X46, X47, X48, X49, X50, X51, X52, X53, X54, X55, X56, X57, X58, X59, X60, X61]:(((~r2_hidden(X50,X49)|(X50=X40|X50=X41|X50=X42|X50=X43|X50=X44|X50=X45|X50=X46|X50=X47|X50=X48)|X49!=k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48))&(((((((((X51!=X40|r2_hidden(X51,X49)|X49!=k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48))&(X51!=X41|r2_hidden(X51,X49)|X49!=k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48)))&(X51!=X42|r2_hidden(X51,X49)|X49!=k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48)))&(X51!=X43|r2_hidden(X51,X49)|X49!=k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48)))&(X51!=X44|r2_hidden(X51,X49)|X49!=k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48)))&(X51!=X45|r2_hidden(X51,X49)|X49!=k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48)))&(X51!=X46|r2_hidden(X51,X49)|X49!=k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48)))&(X51!=X47|r2_hidden(X51,X49)|X49!=k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48)))&(X51!=X48|r2_hidden(X51,X49)|X49!=k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48))))&((((((((((esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61)!=X52|~r2_hidden(esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61),X61)|X61=k7_enumset1(X52,X53,X54,X55,X56,X57,X58,X59,X60))&(esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61)!=X53|~r2_hidden(esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61),X61)|X61=k7_enumset1(X52,X53,X54,X55,X56,X57,X58,X59,X60)))&(esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61)!=X54|~r2_hidden(esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61),X61)|X61=k7_enumset1(X52,X53,X54,X55,X56,X57,X58,X59,X60)))&(esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61)!=X55|~r2_hidden(esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61),X61)|X61=k7_enumset1(X52,X53,X54,X55,X56,X57,X58,X59,X60)))&(esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61)!=X56|~r2_hidden(esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61),X61)|X61=k7_enumset1(X52,X53,X54,X55,X56,X57,X58,X59,X60)))&(esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61)!=X57|~r2_hidden(esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61),X61)|X61=k7_enumset1(X52,X53,X54,X55,X56,X57,X58,X59,X60)))&(esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61)!=X58|~r2_hidden(esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61),X61)|X61=k7_enumset1(X52,X53,X54,X55,X56,X57,X58,X59,X60)))&(esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61)!=X59|~r2_hidden(esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61),X61)|X61=k7_enumset1(X52,X53,X54,X55,X56,X57,X58,X59,X60)))&(esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61)!=X60|~r2_hidden(esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61),X61)|X61=k7_enumset1(X52,X53,X54,X55,X56,X57,X58,X59,X60)))&(r2_hidden(esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61),X61)|(esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61)=X52|esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61)=X53|esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61)=X54|esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61)=X55|esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61)=X56|esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61)=X57|esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61)=X58|esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61)=X59|esk2_10(X52,X53,X54,X55,X56,X57,X58,X59,X60,X61)=X60)|X61=k7_enumset1(X52,X53,X54,X55,X56,X57,X58,X59,X60)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_enumset1])])])])])])).
% 9.28/9.48  cnf(c_0_74, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43])).
% 9.28/9.48  cnf(c_0_75, negated_conjecture, (k3_xboole_0(esk4_0,k3_tarski(k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))=k3_tarski(k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_71]), c_0_62])).
% 9.28/9.48  cnf(c_0_76, plain, (k3_xboole_0(X1,k3_tarski(k7_enumset1(X1,X1,X1,X1,X1,X1,X1,X1,X2)))=X1), inference(spm,[status(thm)],[c_0_72, c_0_55])).
% 9.28/9.48  cnf(c_0_77, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k7_enumset1(X4,X5,X6,X7,X8,X9,X10,X11,X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 9.28/9.48  cnf(c_0_78, plain, (r2_hidden(X1,X2)|X2!=k3_tarski(k7_enumset1(X3,X3,X3,X3,X3,X3,X3,X3,X4))|~r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_74, c_0_55])).
% 9.28/9.48  cnf(c_0_79, negated_conjecture, (k3_tarski(k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))=esk4_0), inference(rw,[status(thm)],[c_0_75, c_0_76])).
% 9.28/9.48  cnf(c_0_80, plain, (r2_hidden(X1,X2)|X2!=k7_enumset1(X3,X4,X5,X6,X7,X8,X9,X10,X1)), inference(er,[status(thm)],[c_0_77])).
% 9.28/9.48  cnf(c_0_81, negated_conjecture, (r2_hidden(X1,X2)|X2!=esk4_0|~r2_hidden(X1,k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 9.28/9.48  cnf(c_0_82, plain, (r2_hidden(X1,k7_enumset1(X2,X3,X4,X5,X6,X7,X8,X9,X1))), inference(er,[status(thm)],[c_0_80])).
% 9.28/9.48  cnf(c_0_83, negated_conjecture, (r2_hidden(esk3_0,X1)|X1!=esk4_0), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 9.28/9.48  cnf(c_0_84, negated_conjecture, (~r2_hidden(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 9.28/9.48  cnf(c_0_85, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_83]), c_0_84]), ['proof']).
% 9.28/9.48  # SZS output end CNFRefutation
% 9.28/9.48  # Proof object total steps             : 86
% 9.28/9.48  # Proof object clause steps            : 45
% 9.28/9.48  # Proof object formula steps           : 41
% 9.28/9.48  # Proof object conjectures             : 15
% 9.28/9.48  # Proof object clause conjectures      : 12
% 9.28/9.48  # Proof object formula conjectures     : 3
% 9.28/9.48  # Proof object initial clauses used    : 21
% 9.28/9.48  # Proof object initial formulas used   : 20
% 9.28/9.48  # Proof object generating inferences   : 10
% 9.28/9.48  # Proof object simplifying inferences  : 113
% 9.28/9.48  # Training examples: 0 positive, 0 negative
% 9.28/9.48  # Parsed axioms                        : 22
% 9.28/9.48  # Removed by relevancy pruning/SinE    : 0
% 9.28/9.48  # Initial clauses                      : 47
% 9.28/9.48  # Removed in clause preprocessing      : 9
% 9.28/9.48  # Initial clauses in saturation        : 38
% 9.28/9.48  # Processed clauses                    : 6482
% 9.28/9.48  # ...of these trivial                  : 661
% 9.28/9.48  # ...subsumed                          : 4974
% 9.28/9.48  # ...remaining for further processing  : 847
% 9.28/9.48  # Other redundant clauses eliminated   : 3784
% 9.28/9.48  # Clauses deleted for lack of memory   : 0
% 9.28/9.48  # Backward-subsumed                    : 18
% 9.28/9.48  # Backward-rewritten                   : 64
% 9.28/9.48  # Generated clauses                    : 408690
% 9.28/9.48  # ...of the previous two non-trivial   : 396272
% 9.28/9.48  # Contextual simplify-reflections      : 0
% 9.28/9.48  # Paramodulations                      : 404085
% 9.28/9.48  # Factorizations                       : 656
% 9.28/9.48  # Equation resolutions                 : 3949
% 9.28/9.48  # Propositional unsat checks           : 0
% 9.28/9.48  #    Propositional check models        : 0
% 9.28/9.48  #    Propositional check unsatisfiable : 0
% 9.28/9.48  #    Propositional clauses             : 0
% 9.28/9.48  #    Propositional clauses after purity: 0
% 9.28/9.48  #    Propositional unsat core size     : 0
% 9.28/9.48  #    Propositional preprocessing time  : 0.000
% 9.28/9.48  #    Propositional encoding time       : 0.000
% 9.28/9.48  #    Propositional solver time         : 0.000
% 9.28/9.48  #    Success case prop preproc time    : 0.000
% 9.28/9.48  #    Success case prop encoding time   : 0.000
% 9.28/9.48  #    Success case prop solver time     : 0.000
% 9.28/9.48  # Current number of processed clauses  : 754
% 9.28/9.48  #    Positive orientable unit clauses  : 216
% 9.28/9.48  #    Positive unorientable unit clauses: 23
% 9.28/9.48  #    Negative unit clauses             : 1
% 9.28/9.48  #    Non-unit-clauses                  : 514
% 9.28/9.48  # Current number of unprocessed clauses: 389441
% 9.28/9.48  # ...number of literals in the above   : 2458169
% 9.28/9.48  # Current number of archived formulas  : 0
% 9.28/9.48  # Current number of archived clauses   : 91
% 9.28/9.48  # Clause-clause subsumption calls (NU) : 117330
% 9.28/9.48  # Rec. Clause-clause subsumption calls : 75917
% 9.28/9.48  # Non-unit clause-clause subsumptions  : 4647
% 9.28/9.48  # Unit Clause-clause subsumption calls : 7655
% 9.28/9.48  # Rewrite failures with RHS unbound    : 0
% 9.28/9.48  # BW rewrite match attempts            : 2352
% 9.28/9.48  # BW rewrite match successes           : 365
% 9.28/9.48  # Condensation attempts                : 0
% 9.28/9.48  # Condensation successes               : 0
% 9.28/9.48  # Termbank termtop insertions          : 13949619
% 9.34/9.50  
% 9.34/9.50  # -------------------------------------------------
% 9.34/9.50  # User time                : 8.930 s
% 9.34/9.50  # System time              : 0.236 s
% 9.34/9.50  # Total time               : 9.166 s
% 9.34/9.50  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
