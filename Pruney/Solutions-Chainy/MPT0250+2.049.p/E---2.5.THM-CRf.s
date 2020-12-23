%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:40:13 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 496 expanded)
%              Number of clauses        :   42 ( 188 expanded)
%              Number of leaves         :   20 ( 153 expanded)
%              Depth                    :   10
%              Number of atoms          :  217 ( 633 expanded)
%              Number of equality atoms :  138 ( 548 expanded)
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

fof(t68_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

fof(t134_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_enumset1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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
    ! [X104,X105] : k3_tarski(k2_tarski(X104,X105)) = k2_xboole_0(X104,X105) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_22,plain,(
    ! [X77,X78] : k1_enumset1(X77,X77,X78) = k2_tarski(X77,X78) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(esk3_0),esk4_0),esk4_0)
    & ~ r2_hidden(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_24,plain,(
    ! [X76] : k2_tarski(X76,X76) = k1_tarski(X76) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_25,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_27,plain,(
    ! [X79,X80,X81] : k2_enumset1(X79,X79,X80,X81) = k1_enumset1(X79,X80,X81) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_28,plain,(
    ! [X82,X83,X84,X85] : k3_enumset1(X82,X82,X83,X84,X85) = k2_enumset1(X82,X83,X84,X85) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_29,plain,(
    ! [X86,X87,X88,X89,X90] : k4_enumset1(X86,X86,X87,X88,X89,X90) = k3_enumset1(X86,X87,X88,X89,X90) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_30,plain,(
    ! [X91,X92,X93,X94,X95,X96] : k5_enumset1(X91,X91,X92,X93,X94,X95,X96) = k4_enumset1(X91,X92,X93,X94,X95,X96) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_31,plain,(
    ! [X97,X98,X99,X100,X101,X102,X103] : k6_enumset1(X97,X97,X98,X99,X100,X101,X102,X103) = k5_enumset1(X97,X98,X99,X100,X101,X102,X103) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_32,plain,(
    ! [X34,X35] : k2_xboole_0(X34,X35) = k5_xboole_0(X34,k4_xboole_0(X35,X34)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_33,plain,(
    ! [X27,X28] : k4_xboole_0(X27,X28) = k5_xboole_0(X27,k3_xboole_0(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_34,plain,(
    ! [X68,X69,X70,X71,X72,X73,X74,X75] : k6_enumset1(X68,X69,X70,X71,X72,X73,X74,X75) = k2_xboole_0(k5_enumset1(X68,X69,X70,X71,X72,X73,X74),k1_tarski(X75)) ),
    inference(variable_rename,[status(thm)],[t68_enumset1])).

fof(c_0_35,plain,(
    ! [X59,X60,X61,X62,X63,X64,X65,X66,X67] : k7_enumset1(X59,X60,X61,X62,X63,X64,X65,X66,X67) = k2_xboole_0(k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66),k1_tarski(X67)) ),
    inference(variable_rename,[status(thm)],[t134_enumset1])).

fof(c_0_36,plain,(
    ! [X29,X30] : r1_tarski(X29,k2_xboole_0(X29,X30)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_37,plain,(
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

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(esk3_0),esk4_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_39,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_40,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_41,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_45,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_48,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_49,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_50,plain,(
    ! [X14,X15] : k5_xboole_0(X14,X15) = k5_xboole_0(X15,X14) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_51,plain,(
    ! [X31,X32,X33] : k5_xboole_0(k5_xboole_0(X31,X32),X33) = k5_xboole_0(X31,k5_xboole_0(X32,X33)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_26]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45])).

cnf(c_0_55,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_40]),c_0_47]),c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45])).

cnf(c_0_56,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_39]),c_0_26]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45])).

cnf(c_0_57,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k3_tarski(k6_enumset1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_39]),c_0_26]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_45]),c_0_45])).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45])).

fof(c_0_61,plain,(
    ! [X12,X13] : k3_xboole_0(X12,X13) = k3_xboole_0(X13,X12) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45])).

fof(c_0_63,plain,(
    ! [X25,X26] :
      ( ( r1_tarski(X25,X26)
        | X25 != X26 )
      & ( r1_tarski(X26,X25)
        | X25 != X26 )
      & ( ~ r1_tarski(X25,X26)
        | ~ r1_tarski(X26,X25)
        | X25 = X26 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))),esk4_0) ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_65,plain,
    ( k7_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_55])).

cnf(c_0_68,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X2)
    | X2 != k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3)))
    | ~ r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_62,c_0_55])).

cnf(c_0_70,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk4_0,k5_xboole_0(k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(esk4_0,k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65]),c_0_65]),c_0_66]),c_0_58])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

fof(c_0_73,plain,(
    ! [X36,X37,X38,X39,X40,X41,X42,X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53,X54,X55,X56,X57] :
      ( ( ~ r2_hidden(X46,X45)
        | X46 = X36
        | X46 = X37
        | X46 = X38
        | X46 = X39
        | X46 = X40
        | X46 = X41
        | X46 = X42
        | X46 = X43
        | X46 = X44
        | X45 != k7_enumset1(X36,X37,X38,X39,X40,X41,X42,X43,X44) )
      & ( X47 != X36
        | r2_hidden(X47,X45)
        | X45 != k7_enumset1(X36,X37,X38,X39,X40,X41,X42,X43,X44) )
      & ( X47 != X37
        | r2_hidden(X47,X45)
        | X45 != k7_enumset1(X36,X37,X38,X39,X40,X41,X42,X43,X44) )
      & ( X47 != X38
        | r2_hidden(X47,X45)
        | X45 != k7_enumset1(X36,X37,X38,X39,X40,X41,X42,X43,X44) )
      & ( X47 != X39
        | r2_hidden(X47,X45)
        | X45 != k7_enumset1(X36,X37,X38,X39,X40,X41,X42,X43,X44) )
      & ( X47 != X40
        | r2_hidden(X47,X45)
        | X45 != k7_enumset1(X36,X37,X38,X39,X40,X41,X42,X43,X44) )
      & ( X47 != X41
        | r2_hidden(X47,X45)
        | X45 != k7_enumset1(X36,X37,X38,X39,X40,X41,X42,X43,X44) )
      & ( X47 != X42
        | r2_hidden(X47,X45)
        | X45 != k7_enumset1(X36,X37,X38,X39,X40,X41,X42,X43,X44) )
      & ( X47 != X43
        | r2_hidden(X47,X45)
        | X45 != k7_enumset1(X36,X37,X38,X39,X40,X41,X42,X43,X44) )
      & ( X47 != X44
        | r2_hidden(X47,X45)
        | X45 != k7_enumset1(X36,X37,X38,X39,X40,X41,X42,X43,X44) )
      & ( esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57) != X48
        | ~ r2_hidden(esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57),X57)
        | X57 = k7_enumset1(X48,X49,X50,X51,X52,X53,X54,X55,X56) )
      & ( esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57) != X49
        | ~ r2_hidden(esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57),X57)
        | X57 = k7_enumset1(X48,X49,X50,X51,X52,X53,X54,X55,X56) )
      & ( esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57) != X50
        | ~ r2_hidden(esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57),X57)
        | X57 = k7_enumset1(X48,X49,X50,X51,X52,X53,X54,X55,X56) )
      & ( esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57) != X51
        | ~ r2_hidden(esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57),X57)
        | X57 = k7_enumset1(X48,X49,X50,X51,X52,X53,X54,X55,X56) )
      & ( esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57) != X52
        | ~ r2_hidden(esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57),X57)
        | X57 = k7_enumset1(X48,X49,X50,X51,X52,X53,X54,X55,X56) )
      & ( esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57) != X53
        | ~ r2_hidden(esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57),X57)
        | X57 = k7_enumset1(X48,X49,X50,X51,X52,X53,X54,X55,X56) )
      & ( esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57) != X54
        | ~ r2_hidden(esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57),X57)
        | X57 = k7_enumset1(X48,X49,X50,X51,X52,X53,X54,X55,X56) )
      & ( esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57) != X55
        | ~ r2_hidden(esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57),X57)
        | X57 = k7_enumset1(X48,X49,X50,X51,X52,X53,X54,X55,X56) )
      & ( esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57) != X56
        | ~ r2_hidden(esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57),X57)
        | X57 = k7_enumset1(X48,X49,X50,X51,X52,X53,X54,X55,X56) )
      & ( r2_hidden(esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57),X57)
        | esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57) = X48
        | esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57) = X49
        | esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57) = X50
        | esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57) = X51
        | esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57) = X52
        | esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57) = X53
        | esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57) = X54
        | esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57) = X55
        | esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57) = X56
        | X57 = k7_enumset1(X48,X49,X50,X51,X52,X53,X54,X55,X56) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_enumset1])])])])])])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,X2)
    | X2 != k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X3,X4)))
    | ~ r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_69,c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( k5_xboole_0(esk4_0,k5_xboole_0(k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(esk4_0,k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k7_enumset1(X4,X5,X6,X7,X8,X9,X10,X11,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(X1,X2)
    | X2 != esk4_0
    | ~ r2_hidden(X1,k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,X2)
    | X2 != k7_enumset1(X3,X4,X5,X6,X7,X8,X9,X10,X1) ),
    inference(er,[status(thm)],[c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(er,[status(thm)],[c_0_77])).

cnf(c_0_80,plain,
    ( r2_hidden(X1,k7_enumset1(X2,X3,X4,X5,X6,X7,X8,X9,X1)) ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:50:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.42  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.19/0.42  # and selection function SelectNegativeLiterals.
% 0.19/0.42  #
% 0.19/0.42  # Preprocessing time       : 0.029 s
% 0.19/0.42  
% 0.19/0.42  # Proof found!
% 0.19/0.42  # SZS status Theorem
% 0.19/0.42  # SZS output start CNFRefutation
% 0.19/0.42  fof(t45_zfmisc_1, conjecture, ![X1, X2]:(r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 0.19/0.42  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.42  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.42  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.42  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.42  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.42  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.42  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.42  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.19/0.42  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.19/0.42  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.42  fof(t68_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_enumset1)).
% 0.19/0.42  fof(t134_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_enumset1)).
% 0.19/0.42  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.42  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.19/0.42  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.19/0.42  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.19/0.42  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.42  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.42  fof(d7_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9, X10]:(X10=k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)<=>![X11]:(r2_hidden(X11,X10)<=>~(((((((((X11!=X1&X11!=X2)&X11!=X3)&X11!=X4)&X11!=X5)&X11!=X6)&X11!=X7)&X11!=X8)&X11!=X9)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_enumset1)).
% 0.19/0.42  fof(c_0_20, negated_conjecture, ~(![X1, X2]:(r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)=>r2_hidden(X1,X2))), inference(assume_negation,[status(cth)],[t45_zfmisc_1])).
% 0.19/0.42  fof(c_0_21, plain, ![X104, X105]:k3_tarski(k2_tarski(X104,X105))=k2_xboole_0(X104,X105), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.42  fof(c_0_22, plain, ![X77, X78]:k1_enumset1(X77,X77,X78)=k2_tarski(X77,X78), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.42  fof(c_0_23, negated_conjecture, (r1_tarski(k2_xboole_0(k1_tarski(esk3_0),esk4_0),esk4_0)&~r2_hidden(esk3_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.19/0.42  fof(c_0_24, plain, ![X76]:k2_tarski(X76,X76)=k1_tarski(X76), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.42  cnf(c_0_25, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.42  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.42  fof(c_0_27, plain, ![X79, X80, X81]:k2_enumset1(X79,X79,X80,X81)=k1_enumset1(X79,X80,X81), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.42  fof(c_0_28, plain, ![X82, X83, X84, X85]:k3_enumset1(X82,X82,X83,X84,X85)=k2_enumset1(X82,X83,X84,X85), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.42  fof(c_0_29, plain, ![X86, X87, X88, X89, X90]:k4_enumset1(X86,X86,X87,X88,X89,X90)=k3_enumset1(X86,X87,X88,X89,X90), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.42  fof(c_0_30, plain, ![X91, X92, X93, X94, X95, X96]:k5_enumset1(X91,X91,X92,X93,X94,X95,X96)=k4_enumset1(X91,X92,X93,X94,X95,X96), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.42  fof(c_0_31, plain, ![X97, X98, X99, X100, X101, X102, X103]:k6_enumset1(X97,X97,X98,X99,X100,X101,X102,X103)=k5_enumset1(X97,X98,X99,X100,X101,X102,X103), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.19/0.42  fof(c_0_32, plain, ![X34, X35]:k2_xboole_0(X34,X35)=k5_xboole_0(X34,k4_xboole_0(X35,X34)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.19/0.42  fof(c_0_33, plain, ![X27, X28]:k4_xboole_0(X27,X28)=k5_xboole_0(X27,k3_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.42  fof(c_0_34, plain, ![X68, X69, X70, X71, X72, X73, X74, X75]:k6_enumset1(X68,X69,X70,X71,X72,X73,X74,X75)=k2_xboole_0(k5_enumset1(X68,X69,X70,X71,X72,X73,X74),k1_tarski(X75)), inference(variable_rename,[status(thm)],[t68_enumset1])).
% 0.19/0.42  fof(c_0_35, plain, ![X59, X60, X61, X62, X63, X64, X65, X66, X67]:k7_enumset1(X59,X60,X61,X62,X63,X64,X65,X66,X67)=k2_xboole_0(k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66),k1_tarski(X67)), inference(variable_rename,[status(thm)],[t134_enumset1])).
% 0.19/0.42  fof(c_0_36, plain, ![X29, X30]:r1_tarski(X29,k2_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.42  fof(c_0_37, plain, ![X16, X17, X18, X19, X20, X21, X22, X23]:(((~r2_hidden(X19,X18)|(r2_hidden(X19,X16)|r2_hidden(X19,X17))|X18!=k2_xboole_0(X16,X17))&((~r2_hidden(X20,X16)|r2_hidden(X20,X18)|X18!=k2_xboole_0(X16,X17))&(~r2_hidden(X20,X17)|r2_hidden(X20,X18)|X18!=k2_xboole_0(X16,X17))))&(((~r2_hidden(esk1_3(X21,X22,X23),X21)|~r2_hidden(esk1_3(X21,X22,X23),X23)|X23=k2_xboole_0(X21,X22))&(~r2_hidden(esk1_3(X21,X22,X23),X22)|~r2_hidden(esk1_3(X21,X22,X23),X23)|X23=k2_xboole_0(X21,X22)))&(r2_hidden(esk1_3(X21,X22,X23),X23)|(r2_hidden(esk1_3(X21,X22,X23),X21)|r2_hidden(esk1_3(X21,X22,X23),X22))|X23=k2_xboole_0(X21,X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.19/0.42  cnf(c_0_38, negated_conjecture, (r1_tarski(k2_xboole_0(k1_tarski(esk3_0),esk4_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.42  cnf(c_0_39, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.42  cnf(c_0_40, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.42  cnf(c_0_41, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.42  cnf(c_0_42, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.42  cnf(c_0_43, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.42  cnf(c_0_44, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.42  cnf(c_0_45, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.42  cnf(c_0_46, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.42  cnf(c_0_47, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.42  cnf(c_0_48, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.42  cnf(c_0_49, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.42  fof(c_0_50, plain, ![X14, X15]:k5_xboole_0(X14,X15)=k5_xboole_0(X15,X14), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.19/0.42  fof(c_0_51, plain, ![X31, X32, X33]:k5_xboole_0(k5_xboole_0(X31,X32),X33)=k5_xboole_0(X31,k5_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.19/0.42  cnf(c_0_52, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.42  cnf(c_0_53, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.42  cnf(c_0_54, negated_conjecture, (r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39]), c_0_26]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45])).
% 0.19/0.42  cnf(c_0_55, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_40]), c_0_47]), c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45])).
% 0.19/0.42  cnf(c_0_56, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_39]), c_0_26]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45])).
% 0.19/0.42  cnf(c_0_57, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k3_tarski(k6_enumset1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_39]), c_0_26]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_45]), c_0_45])).
% 0.19/0.42  cnf(c_0_58, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.42  cnf(c_0_59, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.42  cnf(c_0_60, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45])).
% 0.19/0.42  fof(c_0_61, plain, ![X12, X13]:k3_xboole_0(X12,X13)=k3_xboole_0(X13,X12), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.42  cnf(c_0_62, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45])).
% 0.19/0.42  fof(c_0_63, plain, ![X25, X26]:(((r1_tarski(X25,X26)|X25!=X26)&(r1_tarski(X26,X25)|X25!=X26))&(~r1_tarski(X25,X26)|~r1_tarski(X26,X25)|X25=X26)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.42  cnf(c_0_64, negated_conjecture, (r1_tarski(k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))),esk4_0)), inference(rw,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.42  cnf(c_0_65, plain, (k7_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8)=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(rw,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.42  cnf(c_0_66, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X3,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.42  cnf(c_0_67, plain, (r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(spm,[status(thm)],[c_0_60, c_0_55])).
% 0.19/0.42  cnf(c_0_68, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.42  cnf(c_0_69, plain, (r2_hidden(X1,X2)|X2!=k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3)))|~r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_62, c_0_55])).
% 0.19/0.42  cnf(c_0_70, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.42  cnf(c_0_71, negated_conjecture, (r1_tarski(k5_xboole_0(esk4_0,k5_xboole_0(k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(esk4_0,k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65]), c_0_65]), c_0_66]), c_0_58])).
% 0.19/0.42  cnf(c_0_72, plain, (r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.19/0.42  fof(c_0_73, plain, ![X36, X37, X38, X39, X40, X41, X42, X43, X44, X45, X46, X47, X48, X49, X50, X51, X52, X53, X54, X55, X56, X57]:(((~r2_hidden(X46,X45)|(X46=X36|X46=X37|X46=X38|X46=X39|X46=X40|X46=X41|X46=X42|X46=X43|X46=X44)|X45!=k7_enumset1(X36,X37,X38,X39,X40,X41,X42,X43,X44))&(((((((((X47!=X36|r2_hidden(X47,X45)|X45!=k7_enumset1(X36,X37,X38,X39,X40,X41,X42,X43,X44))&(X47!=X37|r2_hidden(X47,X45)|X45!=k7_enumset1(X36,X37,X38,X39,X40,X41,X42,X43,X44)))&(X47!=X38|r2_hidden(X47,X45)|X45!=k7_enumset1(X36,X37,X38,X39,X40,X41,X42,X43,X44)))&(X47!=X39|r2_hidden(X47,X45)|X45!=k7_enumset1(X36,X37,X38,X39,X40,X41,X42,X43,X44)))&(X47!=X40|r2_hidden(X47,X45)|X45!=k7_enumset1(X36,X37,X38,X39,X40,X41,X42,X43,X44)))&(X47!=X41|r2_hidden(X47,X45)|X45!=k7_enumset1(X36,X37,X38,X39,X40,X41,X42,X43,X44)))&(X47!=X42|r2_hidden(X47,X45)|X45!=k7_enumset1(X36,X37,X38,X39,X40,X41,X42,X43,X44)))&(X47!=X43|r2_hidden(X47,X45)|X45!=k7_enumset1(X36,X37,X38,X39,X40,X41,X42,X43,X44)))&(X47!=X44|r2_hidden(X47,X45)|X45!=k7_enumset1(X36,X37,X38,X39,X40,X41,X42,X43,X44))))&((((((((((esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57)!=X48|~r2_hidden(esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57),X57)|X57=k7_enumset1(X48,X49,X50,X51,X52,X53,X54,X55,X56))&(esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57)!=X49|~r2_hidden(esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57),X57)|X57=k7_enumset1(X48,X49,X50,X51,X52,X53,X54,X55,X56)))&(esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57)!=X50|~r2_hidden(esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57),X57)|X57=k7_enumset1(X48,X49,X50,X51,X52,X53,X54,X55,X56)))&(esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57)!=X51|~r2_hidden(esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57),X57)|X57=k7_enumset1(X48,X49,X50,X51,X52,X53,X54,X55,X56)))&(esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57)!=X52|~r2_hidden(esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57),X57)|X57=k7_enumset1(X48,X49,X50,X51,X52,X53,X54,X55,X56)))&(esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57)!=X53|~r2_hidden(esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57),X57)|X57=k7_enumset1(X48,X49,X50,X51,X52,X53,X54,X55,X56)))&(esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57)!=X54|~r2_hidden(esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57),X57)|X57=k7_enumset1(X48,X49,X50,X51,X52,X53,X54,X55,X56)))&(esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57)!=X55|~r2_hidden(esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57),X57)|X57=k7_enumset1(X48,X49,X50,X51,X52,X53,X54,X55,X56)))&(esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57)!=X56|~r2_hidden(esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57),X57)|X57=k7_enumset1(X48,X49,X50,X51,X52,X53,X54,X55,X56)))&(r2_hidden(esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57),X57)|(esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57)=X48|esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57)=X49|esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57)=X50|esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57)=X51|esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57)=X52|esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57)=X53|esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57)=X54|esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57)=X55|esk2_10(X48,X49,X50,X51,X52,X53,X54,X55,X56,X57)=X56)|X57=k7_enumset1(X48,X49,X50,X51,X52,X53,X54,X55,X56)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_enumset1])])])])])])).
% 0.19/0.42  cnf(c_0_74, plain, (r2_hidden(X1,X2)|X2!=k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X3,X4)))|~r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_69, c_0_68])).
% 0.19/0.42  cnf(c_0_75, negated_conjecture, (k5_xboole_0(esk4_0,k5_xboole_0(k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(esk4_0,k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72])])).
% 0.19/0.42  cnf(c_0_76, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k7_enumset1(X4,X5,X6,X7,X8,X9,X10,X11,X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.19/0.42  cnf(c_0_77, negated_conjecture, (r2_hidden(X1,X2)|X2!=esk4_0|~r2_hidden(X1,k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.19/0.42  cnf(c_0_78, plain, (r2_hidden(X1,X2)|X2!=k7_enumset1(X3,X4,X5,X6,X7,X8,X9,X10,X1)), inference(er,[status(thm)],[c_0_76])).
% 0.19/0.42  cnf(c_0_79, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(er,[status(thm)],[c_0_77])).
% 0.19/0.42  cnf(c_0_80, plain, (r2_hidden(X1,k7_enumset1(X2,X3,X4,X5,X6,X7,X8,X9,X1))), inference(er,[status(thm)],[c_0_78])).
% 0.19/0.42  cnf(c_0_81, negated_conjecture, (~r2_hidden(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.42  cnf(c_0_82, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 83
% 0.19/0.42  # Proof object clause steps            : 42
% 0.19/0.42  # Proof object formula steps           : 41
% 0.19/0.42  # Proof object conjectures             : 12
% 0.19/0.42  # Proof object clause conjectures      : 9
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 21
% 0.19/0.42  # Proof object initial formulas used   : 20
% 0.19/0.42  # Proof object generating inferences   : 10
% 0.19/0.42  # Proof object simplifying inferences  : 90
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 20
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 47
% 0.19/0.42  # Removed in clause preprocessing      : 9
% 0.19/0.42  # Initial clauses in saturation        : 38
% 0.19/0.42  # Processed clauses                    : 282
% 0.19/0.42  # ...of these trivial                  : 10
% 0.19/0.42  # ...subsumed                          : 133
% 0.19/0.42  # ...remaining for further processing  : 139
% 0.19/0.42  # Other redundant clauses eliminated   : 39
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 0
% 0.19/0.42  # Backward-rewritten                   : 6
% 0.19/0.42  # Generated clauses                    : 2203
% 0.19/0.42  # ...of the previous two non-trivial   : 2126
% 0.19/0.42  # Contextual simplify-reflections      : 0
% 0.19/0.42  # Paramodulations                      : 2112
% 0.19/0.42  # Factorizations                       : 4
% 0.19/0.42  # Equation resolutions                 : 87
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 122
% 0.19/0.42  #    Positive orientable unit clauses  : 20
% 0.19/0.42  #    Positive unorientable unit clauses: 11
% 0.19/0.42  #    Negative unit clauses             : 1
% 0.19/0.42  #    Non-unit-clauses                  : 90
% 0.19/0.42  # Current number of unprocessed clauses: 1851
% 0.19/0.42  # ...number of literals in the above   : 6617
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 15
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 3621
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 2838
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 95
% 0.19/0.42  # Unit Clause-clause subsumption calls : 51
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 151
% 0.19/0.42  # BW rewrite match successes           : 86
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 34680
% 0.19/0.43  
% 0.19/0.43  # -------------------------------------------------
% 0.19/0.43  # User time                : 0.084 s
% 0.19/0.43  # System time              : 0.005 s
% 0.19/0.43  # Total time               : 0.088 s
% 0.19/0.43  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
