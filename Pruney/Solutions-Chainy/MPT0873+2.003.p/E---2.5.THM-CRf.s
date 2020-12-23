%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:37 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 (1857 expanded)
%              Number of clauses        :   50 ( 747 expanded)
%              Number of leaves         :   14 ( 551 expanded)
%              Depth                    :   14
%              Number of atoms          :  153 (2522 expanded)
%              Number of equality atoms :  104 (2303 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ! [X2] :
          ( X2 = k1_mcart_1(X1)
        <=> ! [X3,X4] :
              ( X1 = k4_tarski(X3,X4)
             => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_mcart_1)).

fof(t33_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k4_mcart_1(X1,X2,X3,X4) = k4_mcart_1(X5,X6,X7,X8)
     => ( X1 = X5
        & X2 = X6
        & X3 = X7
        & X4 = X8 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_mcart_1)).

fof(t31_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

fof(t55_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(t76_enumset1,axiom,(
    ! [X1] : k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(t93_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_zfmisc_1)).

fof(t78_enumset1,axiom,(
    ! [X1,X2,X3] : k3_enumset1(X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).

fof(t88_enumset1,axiom,(
    ! [X1,X2] : k4_enumset1(X1,X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_enumset1)).

fof(t86_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_enumset1)).

fof(t66_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).

fof(t129_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X4)))
    <=> ( r2_hidden(X1,X3)
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(t16_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),k1_tarski(X2))
        & X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(t13_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,k1_tarski(X3)))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & k2_mcart_1(X1) = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).

fof(t57_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X3,X2)
        & ~ r1_xboole_0(k2_tarski(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(c_0_14,plain,(
    ! [X45,X46,X47,X48,X49,X50,X51] :
      ( ( X48 != k1_mcart_1(X45)
        | X45 != k4_tarski(X49,X50)
        | X48 = X49
        | X45 != k4_tarski(X46,X47) )
      & ( X45 = k4_tarski(esk1_2(X45,X51),esk2_2(X45,X51))
        | X51 = k1_mcart_1(X45)
        | X45 != k4_tarski(X46,X47) )
      & ( X51 != esk1_2(X45,X51)
        | X51 = k1_mcart_1(X45)
        | X45 != k4_tarski(X46,X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_mcart_1])])])])])])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] :
        ( k4_mcart_1(X1,X2,X3,X4) = k4_mcart_1(X5,X6,X7,X8)
       => ( X1 = X5
          & X2 = X6
          & X3 = X7
          & X4 = X8 ) ) ),
    inference(assume_negation,[status(cth)],[t33_mcart_1])).

cnf(c_0_16,plain,
    ( X1 = X3
    | X1 != k1_mcart_1(X2)
    | X2 != k4_tarski(X3,X4)
    | X2 != k4_tarski(X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_17,negated_conjecture,
    ( k4_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = k4_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0)
    & ( esk3_0 != esk7_0
      | esk4_0 != esk8_0
      | esk5_0 != esk9_0
      | esk6_0 != esk10_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_18,plain,(
    ! [X57,X58,X59,X60] : k4_mcart_1(X57,X58,X59,X60) = k4_tarski(k4_tarski(k4_tarski(X57,X58),X59),X60) ),
    inference(variable_rename,[status(thm)],[t31_mcart_1])).

cnf(c_0_19,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X3
    | k4_tarski(X1,X2) != k4_tarski(X3,X4) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_16])])).

cnf(c_0_20,negated_conjecture,
    ( k4_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = k4_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X9,X10,X11,X12,X13,X14] : k4_enumset1(X9,X10,X11,X12,X13,X14) = k2_xboole_0(k3_enumset1(X9,X10,X11,X12,X13),k1_tarski(X14)) ),
    inference(variable_rename,[status(thm)],[t55_enumset1])).

fof(c_0_23,plain,(
    ! [X23] : k1_enumset1(X23,X23,X23) = k1_tarski(X23) ),
    inference(variable_rename,[status(thm)],[t76_enumset1])).

fof(c_0_24,plain,(
    ! [X43,X44] : k3_tarski(k2_tarski(X43,X44)) = k2_xboole_0(X43,X44) ),
    inference(variable_rename,[status(thm)],[t93_zfmisc_1])).

fof(c_0_25,plain,(
    ! [X24,X25,X26] : k3_enumset1(X24,X24,X24,X25,X26) = k1_enumset1(X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t78_enumset1])).

fof(c_0_26,plain,(
    ! [X32,X33] : k4_enumset1(X32,X32,X32,X32,X32,X33) = k2_tarski(X32,X33) ),
    inference(variable_rename,[status(thm)],[t88_enumset1])).

fof(c_0_27,plain,(
    ! [X27,X28,X29,X30,X31] : k6_enumset1(X27,X27,X27,X27,X28,X29,X30,X31) = k3_enumset1(X27,X28,X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t86_enumset1])).

fof(c_0_28,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22] : k6_enumset1(X15,X16,X17,X18,X19,X20,X21,X22) = k2_xboole_0(k3_enumset1(X15,X16,X17,X18,X19),k1_enumset1(X20,X21,X22)) ),
    inference(variable_rename,[status(thm)],[t66_enumset1])).

cnf(c_0_29,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),esk10_0) = k4_tarski(k4_tarski(k4_tarski(esk3_0,esk4_0),esk5_0),esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_21])).

fof(c_0_31,plain,(
    ! [X34,X35,X36,X37] :
      ( ( r2_hidden(X34,X36)
        | ~ r2_hidden(k4_tarski(X34,X35),k2_zfmisc_1(X36,k1_tarski(X37))) )
      & ( X35 = X37
        | ~ r2_hidden(k4_tarski(X34,X35),k2_zfmisc_1(X36,k1_tarski(X37))) )
      & ( ~ r2_hidden(X34,X36)
        | X35 != X37
        | r2_hidden(k4_tarski(X34,X35),k2_zfmisc_1(X36,k1_tarski(X37))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t129_zfmisc_1])])])).

cnf(c_0_32,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k3_enumset1(X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k4_enumset1(X1,X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( k4_tarski(k4_tarski(esk3_0,esk4_0),esk5_0) = k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_29])).

fof(c_0_40,plain,(
    ! [X38,X39] :
      ( ~ r1_xboole_0(k1_tarski(X38),k1_tarski(X39))
      | X38 != X39 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_zfmisc_1])])).

cnf(c_0_41,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k3_tarski(k4_enumset1(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_43,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k4_enumset1(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( k4_tarski(esk3_0,esk4_0) = k4_tarski(esk7_0,esk8_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_39]),c_0_29])).

cnf(c_0_45,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,k1_tarski(X4)))
    | ~ r2_hidden(X1,X2)
    | X3 != X4 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),k1_tarski(X2))
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_47,plain,(
    ! [X54,X55,X56] :
      ( ( r2_hidden(k1_mcart_1(X54),X55)
        | ~ r2_hidden(X54,k2_zfmisc_1(X55,k1_tarski(X56))) )
      & ( k2_mcart_1(X54) = X56
        | ~ r2_hidden(X54,k2_zfmisc_1(X55,k1_tarski(X56))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_mcart_1])])])).

cnf(c_0_48,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_33]),c_0_35]),c_0_37])).

cnf(c_0_49,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X6,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( esk3_0 = esk7_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_44]),c_0_29])).

cnf(c_0_51,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4)))
    | X3 != X4
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_33]),c_0_35]),c_0_37])).

cnf(c_0_52,plain,
    ( X1 != X2
    | ~ r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_33]),c_0_33]),c_0_35]),c_0_35]),c_0_37]),c_0_37])).

fof(c_0_53,plain,(
    ! [X40,X41,X42] :
      ( r2_hidden(X40,X41)
      | r2_hidden(X42,X41)
      | r1_xboole_0(k2_tarski(X40,X42),X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_zfmisc_1])])])).

cnf(c_0_54,plain,
    ( k2_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k4_enumset1(X2,X2,X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( k4_tarski(esk7_0,esk4_0) = k4_tarski(esk7_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_44,c_0_50])).

cnf(c_0_57,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( ~ r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | r1_xboole_0(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,plain,
    ( k2_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_33]),c_0_35]),c_0_37])).

cnf(c_0_61,negated_conjecture,
    ( esk4_0 = X1
    | ~ r2_hidden(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(X2,k4_enumset1(X1,X1,X1,X1,X1,X1))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k4_enumset1(X2,X2,X2,X2,X2,X2)))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_57,c_0_49])).

cnf(c_0_63,plain,
    ( ~ r1_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_49]),c_0_49])).

cnf(c_0_64,plain,
    ( r2_hidden(X3,X2)
    | r2_hidden(X1,X2)
    | r1_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X3),X2) ),
    inference(rw,[status(thm)],[c_0_59,c_0_36])).

cnf(c_0_65,plain,
    ( k2_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,k4_enumset1(X2,X2,X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[c_0_60,c_0_49])).

cnf(c_0_66,negated_conjecture,
    ( esk3_0 != esk7_0
    | esk4_0 != esk8_0
    | esk5_0 != esk9_0
    | esk6_0 != esk10_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_67,negated_conjecture,
    ( esk4_0 = esk8_0
    | ~ r2_hidden(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,k4_enumset1(X1,X1,X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_69,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_65,c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( esk4_0 != esk8_0
    | esk5_0 != esk9_0
    | esk6_0 != esk10_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_50])])).

cnf(c_0_71,negated_conjecture,
    ( esk4_0 = esk8_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_72,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(spm,[status(thm)],[c_0_69,c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),esk6_0) = k4_tarski(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),esk10_0) ),
    inference(rw,[status(thm)],[c_0_30,c_0_39])).

cnf(c_0_74,negated_conjecture,
    ( esk5_0 != esk9_0
    | esk6_0 != esk10_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71])])).

cnf(c_0_75,negated_conjecture,
    ( esk6_0 = esk10_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( k4_tarski(k4_tarski(esk7_0,esk8_0),esk5_0) = k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0) ),
    inference(rw,[status(thm)],[c_0_39,c_0_44])).

cnf(c_0_77,negated_conjecture,
    ( esk5_0 != esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75])])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_76]),c_0_72]),c_0_77]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:29:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S032I
% 0.20/0.38  # and selection function SelectUnlessUniqMax.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.027 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(d1_mcart_1, axiom, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>![X2]:(X2=k1_mcart_1(X1)<=>![X3, X4]:(X1=k4_tarski(X3,X4)=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_mcart_1)).
% 0.20/0.38  fof(t33_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_mcart_1(X1,X2,X3,X4)=k4_mcart_1(X5,X6,X7,X8)=>(((X1=X5&X2=X6)&X3=X7)&X4=X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_mcart_1)).
% 0.20/0.38  fof(t31_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_mcart_1)).
% 0.20/0.38  fof(t55_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 0.20/0.38  fof(t76_enumset1, axiom, ![X1]:k1_enumset1(X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_enumset1)).
% 0.20/0.38  fof(t93_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_zfmisc_1)).
% 0.20/0.38  fof(t78_enumset1, axiom, ![X1, X2, X3]:k3_enumset1(X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_enumset1)).
% 0.20/0.38  fof(t88_enumset1, axiom, ![X1, X2]:k4_enumset1(X1,X1,X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_enumset1)).
% 0.20/0.38  fof(t86_enumset1, axiom, ![X1, X2, X3, X4, X5]:k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_enumset1)).
% 0.20/0.38  fof(t66_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_enumset1)).
% 0.20/0.38  fof(t129_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X4)))<=>(r2_hidden(X1,X3)&X2=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 0.20/0.38  fof(t16_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),k1_tarski(X2))&X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 0.20/0.38  fof(t13_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,k1_tarski(X3)))=>(r2_hidden(k1_mcart_1(X1),X2)&k2_mcart_1(X1)=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_mcart_1)).
% 0.20/0.38  fof(t57_zfmisc_1, axiom, ![X1, X2, X3]:~(((~(r2_hidden(X1,X2))&~(r2_hidden(X3,X2)))&~(r1_xboole_0(k2_tarski(X1,X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 0.20/0.38  fof(c_0_14, plain, ![X45, X46, X47, X48, X49, X50, X51]:((X48!=k1_mcart_1(X45)|(X45!=k4_tarski(X49,X50)|X48=X49)|X45!=k4_tarski(X46,X47))&((X45=k4_tarski(esk1_2(X45,X51),esk2_2(X45,X51))|X51=k1_mcart_1(X45)|X45!=k4_tarski(X46,X47))&(X51!=esk1_2(X45,X51)|X51=k1_mcart_1(X45)|X45!=k4_tarski(X46,X47)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_mcart_1])])])])])])).
% 0.20/0.38  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_mcart_1(X1,X2,X3,X4)=k4_mcart_1(X5,X6,X7,X8)=>(((X1=X5&X2=X6)&X3=X7)&X4=X8))), inference(assume_negation,[status(cth)],[t33_mcart_1])).
% 0.20/0.38  cnf(c_0_16, plain, (X1=X3|X1!=k1_mcart_1(X2)|X2!=k4_tarski(X3,X4)|X2!=k4_tarski(X5,X6)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  fof(c_0_17, negated_conjecture, (k4_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=k4_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0)&(esk3_0!=esk7_0|esk4_0!=esk8_0|esk5_0!=esk9_0|esk6_0!=esk10_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.20/0.38  fof(c_0_18, plain, ![X57, X58, X59, X60]:k4_mcart_1(X57,X58,X59,X60)=k4_tarski(k4_tarski(k4_tarski(X57,X58),X59),X60), inference(variable_rename,[status(thm)],[t31_mcart_1])).
% 0.20/0.38  cnf(c_0_19, plain, (k1_mcart_1(k4_tarski(X1,X2))=X3|k4_tarski(X1,X2)!=k4_tarski(X3,X4)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_16])])).
% 0.20/0.38  cnf(c_0_20, negated_conjecture, (k4_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=k4_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_21, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  fof(c_0_22, plain, ![X9, X10, X11, X12, X13, X14]:k4_enumset1(X9,X10,X11,X12,X13,X14)=k2_xboole_0(k3_enumset1(X9,X10,X11,X12,X13),k1_tarski(X14)), inference(variable_rename,[status(thm)],[t55_enumset1])).
% 0.20/0.38  fof(c_0_23, plain, ![X23]:k1_enumset1(X23,X23,X23)=k1_tarski(X23), inference(variable_rename,[status(thm)],[t76_enumset1])).
% 0.20/0.38  fof(c_0_24, plain, ![X43, X44]:k3_tarski(k2_tarski(X43,X44))=k2_xboole_0(X43,X44), inference(variable_rename,[status(thm)],[t93_zfmisc_1])).
% 0.20/0.38  fof(c_0_25, plain, ![X24, X25, X26]:k3_enumset1(X24,X24,X24,X25,X26)=k1_enumset1(X24,X25,X26), inference(variable_rename,[status(thm)],[t78_enumset1])).
% 0.20/0.38  fof(c_0_26, plain, ![X32, X33]:k4_enumset1(X32,X32,X32,X32,X32,X33)=k2_tarski(X32,X33), inference(variable_rename,[status(thm)],[t88_enumset1])).
% 0.20/0.38  fof(c_0_27, plain, ![X27, X28, X29, X30, X31]:k6_enumset1(X27,X27,X27,X27,X28,X29,X30,X31)=k3_enumset1(X27,X28,X29,X30,X31), inference(variable_rename,[status(thm)],[t86_enumset1])).
% 0.20/0.38  fof(c_0_28, plain, ![X15, X16, X17, X18, X19, X20, X21, X22]:k6_enumset1(X15,X16,X17,X18,X19,X20,X21,X22)=k2_xboole_0(k3_enumset1(X15,X16,X17,X18,X19),k1_enumset1(X20,X21,X22)), inference(variable_rename,[status(thm)],[t66_enumset1])).
% 0.20/0.38  cnf(c_0_29, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(er,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (k4_tarski(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),esk10_0)=k4_tarski(k4_tarski(k4_tarski(esk3_0,esk4_0),esk5_0),esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_21])).
% 0.20/0.38  fof(c_0_31, plain, ![X34, X35, X36, X37]:(((r2_hidden(X34,X36)|~r2_hidden(k4_tarski(X34,X35),k2_zfmisc_1(X36,k1_tarski(X37))))&(X35=X37|~r2_hidden(k4_tarski(X34,X35),k2_zfmisc_1(X36,k1_tarski(X37)))))&(~r2_hidden(X34,X36)|X35!=X37|r2_hidden(k4_tarski(X34,X35),k2_zfmisc_1(X36,k1_tarski(X37))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t129_zfmisc_1])])])).
% 0.20/0.38  cnf(c_0_32, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.38  cnf(c_0_33, plain, (k1_enumset1(X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_34, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_35, plain, (k3_enumset1(X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.38  cnf(c_0_36, plain, (k4_enumset1(X1,X1,X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_37, plain, (k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.38  cnf(c_0_38, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (k4_tarski(k4_tarski(esk3_0,esk4_0),esk5_0)=k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_29])).
% 0.20/0.38  fof(c_0_40, plain, ![X38, X39]:(~r1_xboole_0(k1_tarski(X38),k1_tarski(X39))|X38!=X39), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_zfmisc_1])])).
% 0.20/0.38  cnf(c_0_41, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.38  cnf(c_0_42, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k3_tarski(k4_enumset1(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 0.20/0.38  cnf(c_0_43, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k3_tarski(k4_enumset1(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, (k4_tarski(esk3_0,esk4_0)=k4_tarski(esk7_0,esk8_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_39]), c_0_29])).
% 0.20/0.38  cnf(c_0_45, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,k1_tarski(X4)))|~r2_hidden(X1,X2)|X3!=X4), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.38  cnf(c_0_46, plain, (~r1_xboole_0(k1_tarski(X1),k1_tarski(X2))|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.38  fof(c_0_47, plain, ![X54, X55, X56]:((r2_hidden(k1_mcart_1(X54),X55)|~r2_hidden(X54,k2_zfmisc_1(X55,k1_tarski(X56))))&(k2_mcart_1(X54)=X56|~r2_hidden(X54,k2_zfmisc_1(X55,k1_tarski(X56))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_mcart_1])])])).
% 0.20/0.38  cnf(c_0_48, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_33]), c_0_35]), c_0_37])).
% 0.20/0.38  cnf(c_0_49, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X6,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.38  cnf(c_0_50, negated_conjecture, (esk3_0=esk7_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_44]), c_0_29])).
% 0.20/0.38  cnf(c_0_51, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4)))|X3!=X4|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_33]), c_0_35]), c_0_37])).
% 0.20/0.38  cnf(c_0_52, plain, (X1!=X2|~r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_33]), c_0_33]), c_0_35]), c_0_35]), c_0_37]), c_0_37])).
% 0.20/0.38  fof(c_0_53, plain, ![X40, X41, X42]:(r2_hidden(X40,X41)|r2_hidden(X42,X41)|r1_xboole_0(k2_tarski(X40,X42),X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_zfmisc_1])])])).
% 0.20/0.38  cnf(c_0_54, plain, (k2_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.38  cnf(c_0_55, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k4_enumset1(X2,X2,X2,X2,X2,X2)))), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.38  cnf(c_0_56, negated_conjecture, (k4_tarski(esk7_0,esk4_0)=k4_tarski(esk7_0,esk8_0)), inference(rw,[status(thm)],[c_0_44, c_0_50])).
% 0.20/0.38  cnf(c_0_57, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_51])).
% 0.20/0.38  cnf(c_0_58, plain, (~r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))), inference(er,[status(thm)],[c_0_52])).
% 0.20/0.38  cnf(c_0_59, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|r1_xboole_0(k2_tarski(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.38  cnf(c_0_60, plain, (k2_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_33]), c_0_35]), c_0_37])).
% 0.20/0.38  cnf(c_0_61, negated_conjecture, (esk4_0=X1|~r2_hidden(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(X2,k4_enumset1(X1,X1,X1,X1,X1,X1)))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.38  cnf(c_0_62, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k4_enumset1(X2,X2,X2,X2,X2,X2)))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_57, c_0_49])).
% 0.20/0.38  cnf(c_0_63, plain, (~r1_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_49]), c_0_49])).
% 0.20/0.38  cnf(c_0_64, plain, (r2_hidden(X3,X2)|r2_hidden(X1,X2)|r1_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X3),X2)), inference(rw,[status(thm)],[c_0_59, c_0_36])).
% 0.20/0.38  cnf(c_0_65, plain, (k2_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(X3,k4_enumset1(X2,X2,X2,X2,X2,X2)))), inference(rw,[status(thm)],[c_0_60, c_0_49])).
% 0.20/0.38  cnf(c_0_66, negated_conjecture, (esk3_0!=esk7_0|esk4_0!=esk8_0|esk5_0!=esk9_0|esk6_0!=esk10_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_67, negated_conjecture, (esk4_0=esk8_0|~r2_hidden(esk7_0,X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.38  cnf(c_0_68, plain, (r2_hidden(X1,k4_enumset1(X1,X1,X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.20/0.38  cnf(c_0_69, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_65, c_0_62])).
% 0.20/0.38  cnf(c_0_70, negated_conjecture, (esk4_0!=esk8_0|esk5_0!=esk9_0|esk6_0!=esk10_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_50])])).
% 0.20/0.38  cnf(c_0_71, negated_conjecture, (esk4_0=esk8_0), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.20/0.38  cnf(c_0_72, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(spm,[status(thm)],[c_0_69, c_0_68])).
% 0.20/0.38  cnf(c_0_73, negated_conjecture, (k4_tarski(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),esk6_0)=k4_tarski(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),esk10_0)), inference(rw,[status(thm)],[c_0_30, c_0_39])).
% 0.20/0.38  cnf(c_0_74, negated_conjecture, (esk5_0!=esk9_0|esk6_0!=esk10_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_71])])).
% 0.20/0.38  cnf(c_0_75, negated_conjecture, (esk6_0=esk10_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_72])).
% 0.20/0.38  cnf(c_0_76, negated_conjecture, (k4_tarski(k4_tarski(esk7_0,esk8_0),esk5_0)=k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0)), inference(rw,[status(thm)],[c_0_39, c_0_44])).
% 0.20/0.38  cnf(c_0_77, negated_conjecture, (esk5_0!=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_75])])).
% 0.20/0.38  cnf(c_0_78, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_76]), c_0_72]), c_0_77]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 79
% 0.20/0.38  # Proof object clause steps            : 50
% 0.20/0.38  # Proof object formula steps           : 29
% 0.20/0.38  # Proof object conjectures             : 20
% 0.20/0.38  # Proof object clause conjectures      : 17
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 16
% 0.20/0.38  # Proof object initial formulas used   : 14
% 0.20/0.38  # Proof object generating inferences   : 12
% 0.20/0.38  # Proof object simplifying inferences  : 62
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 14
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 20
% 0.20/0.38  # Removed in clause preprocessing      : 6
% 0.20/0.38  # Initial clauses in saturation        : 14
% 0.20/0.38  # Processed clauses                    : 81
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 18
% 0.20/0.38  # ...remaining for further processing  : 62
% 0.20/0.38  # Other redundant clauses eliminated   : 6
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 21
% 0.20/0.38  # Generated clauses                    : 78
% 0.20/0.38  # ...of the previous two non-trivial   : 87
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 71
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 8
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 22
% 0.20/0.38  #    Positive orientable unit clauses  : 9
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 2
% 0.20/0.38  #    Non-unit-clauses                  : 11
% 0.20/0.38  # Current number of unprocessed clauses: 28
% 0.20/0.38  # ...number of literals in the above   : 66
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 41
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 76
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 74
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 18
% 0.20/0.38  # Unit Clause-clause subsumption calls : 16
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 19
% 0.20/0.38  # BW rewrite match successes           : 13
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 2451
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.030 s
% 0.20/0.38  # System time              : 0.004 s
% 0.20/0.38  # Total time               : 0.035 s
% 0.20/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
