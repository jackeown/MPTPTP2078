%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:37:09 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 267 expanded)
%              Number of clauses        :   28 ( 100 expanded)
%              Number of leaves         :   13 (  82 expanded)
%              Depth                    :    9
%              Number of atoms          :  165 ( 468 expanded)
%              Number of equality atoms :  137 ( 419 expanded)
%              Maximal formula depth    :   52 (   5 average)
%              Maximal clause size      :   76 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t8_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k1_tarski(X1) = k2_tarski(X2,X3)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_zfmisc_1)).

fof(t134_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

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

fof(t68_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_enumset1)).

fof(c_0_13,plain,(
    ! [X14,X15] : k2_xboole_0(X14,X15) = k5_xboole_0(X14,k4_xboole_0(X15,X14)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_14,plain,(
    ! [X12,X13] : k4_xboole_0(X12,X13) = k5_xboole_0(X12,k3_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k1_tarski(X1) = k2_tarski(X2,X3)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t8_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X39,X40,X41,X42,X43,X44,X45,X46,X47] : k7_enumset1(X39,X40,X41,X42,X43,X44,X45,X46,X47) = k2_xboole_0(k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46),k1_tarski(X47)) ),
    inference(variable_rename,[status(thm)],[t134_enumset1])).

fof(c_0_17,plain,(
    ! [X56] : k2_tarski(X56,X56) = k1_tarski(X56) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_18,plain,(
    ! [X57,X58] : k1_enumset1(X57,X57,X58) = k2_tarski(X57,X58) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X59,X60,X61] : k2_enumset1(X59,X59,X60,X61) = k1_enumset1(X59,X60,X61) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_22,plain,(
    ! [X62,X63,X64,X65] : k3_enumset1(X62,X62,X63,X64,X65) = k2_enumset1(X62,X63,X64,X65) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_23,plain,(
    ! [X66,X67,X68,X69,X70] : k4_enumset1(X66,X66,X67,X68,X69,X70) = k3_enumset1(X66,X67,X68,X69,X70) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_24,plain,(
    ! [X71,X72,X73,X74,X75,X76] : k5_enumset1(X71,X71,X72,X73,X74,X75,X76) = k4_enumset1(X71,X72,X73,X74,X75,X76) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_25,plain,(
    ! [X77,X78,X79,X80,X81,X82,X83] : k6_enumset1(X77,X77,X78,X79,X80,X81,X82,X83) = k5_enumset1(X77,X78,X79,X80,X81,X82,X83) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_26,negated_conjecture,
    ( k1_tarski(esk2_0) = k2_tarski(esk3_0,esk4_0)
    & esk2_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_27,plain,(
    ! [X48,X49,X50,X51,X52,X53,X54,X55] : k6_enumset1(X48,X49,X50,X51,X52,X53,X54,X55) = k2_xboole_0(k5_enumset1(X48,X49,X50,X51,X52,X53,X54),k1_tarski(X55)) ),
    inference(variable_rename,[status(thm)],[t68_enumset1])).

fof(c_0_28,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22,X23,X24,X25,X26,X27,X28,X29,X30,X31,X32,X33,X34,X35,X36,X37] :
      ( ( ~ r2_hidden(X26,X25)
        | X26 = X16
        | X26 = X17
        | X26 = X18
        | X26 = X19
        | X26 = X20
        | X26 = X21
        | X26 = X22
        | X26 = X23
        | X26 = X24
        | X25 != k7_enumset1(X16,X17,X18,X19,X20,X21,X22,X23,X24) )
      & ( X27 != X16
        | r2_hidden(X27,X25)
        | X25 != k7_enumset1(X16,X17,X18,X19,X20,X21,X22,X23,X24) )
      & ( X27 != X17
        | r2_hidden(X27,X25)
        | X25 != k7_enumset1(X16,X17,X18,X19,X20,X21,X22,X23,X24) )
      & ( X27 != X18
        | r2_hidden(X27,X25)
        | X25 != k7_enumset1(X16,X17,X18,X19,X20,X21,X22,X23,X24) )
      & ( X27 != X19
        | r2_hidden(X27,X25)
        | X25 != k7_enumset1(X16,X17,X18,X19,X20,X21,X22,X23,X24) )
      & ( X27 != X20
        | r2_hidden(X27,X25)
        | X25 != k7_enumset1(X16,X17,X18,X19,X20,X21,X22,X23,X24) )
      & ( X27 != X21
        | r2_hidden(X27,X25)
        | X25 != k7_enumset1(X16,X17,X18,X19,X20,X21,X22,X23,X24) )
      & ( X27 != X22
        | r2_hidden(X27,X25)
        | X25 != k7_enumset1(X16,X17,X18,X19,X20,X21,X22,X23,X24) )
      & ( X27 != X23
        | r2_hidden(X27,X25)
        | X25 != k7_enumset1(X16,X17,X18,X19,X20,X21,X22,X23,X24) )
      & ( X27 != X24
        | r2_hidden(X27,X25)
        | X25 != k7_enumset1(X16,X17,X18,X19,X20,X21,X22,X23,X24) )
      & ( esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37) != X28
        | ~ r2_hidden(esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37),X37)
        | X37 = k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36) )
      & ( esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37) != X29
        | ~ r2_hidden(esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37),X37)
        | X37 = k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36) )
      & ( esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37) != X30
        | ~ r2_hidden(esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37),X37)
        | X37 = k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36) )
      & ( esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37) != X31
        | ~ r2_hidden(esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37),X37)
        | X37 = k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36) )
      & ( esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37) != X32
        | ~ r2_hidden(esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37),X37)
        | X37 = k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36) )
      & ( esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37) != X33
        | ~ r2_hidden(esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37),X37)
        | X37 = k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36) )
      & ( esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37) != X34
        | ~ r2_hidden(esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37),X37)
        | X37 = k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36) )
      & ( esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37) != X35
        | ~ r2_hidden(esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37),X37)
        | X37 = k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36) )
      & ( esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37) != X36
        | ~ r2_hidden(esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37),X37)
        | X37 = k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36) )
      & ( r2_hidden(esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37),X37)
        | esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37) = X28
        | esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37) = X29
        | esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37) = X30
        | esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37) = X31
        | esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37) = X32
        | esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37) = X33
        | esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37) = X34
        | esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37) = X35
        | esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37) = X36
        | X37 = k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_enumset1])])])])])])).

cnf(c_0_29,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( k1_tarski(esk2_0) = k2_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k7_enumset1(X4,X5,X6,X7,X8,X9,X2,X10,X11) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k5_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k3_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_30]),c_0_31]),c_0_31]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_43,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X2)
    | X2 != k7_enumset1(X3,X4,X5,X6,X7,X8,X1,X9,X10) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X1) = k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_46,plain,
    ( k7_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[c_0_43,c_0_41])).

cnf(c_0_47,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k7_enumset1(X2,X3,X4,X5,X6,X7,X1,X8,X9)) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,X1) = k7_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X1) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,plain,
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
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk3_0,k7_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_53,negated_conjecture,
    ( esk3_0 = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_52,c_0_53]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:38:55 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.20/0.38  # and selection function SelectNegativeLiterals.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.027 s
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.20/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.38  fof(t8_zfmisc_1, conjecture, ![X1, X2, X3]:(k1_tarski(X1)=k2_tarski(X2,X3)=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_zfmisc_1)).
% 0.20/0.38  fof(t134_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_enumset1)).
% 0.20/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.38  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.38  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.20/0.38  fof(t68_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_enumset1)).
% 0.20/0.38  fof(d7_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9, X10]:(X10=k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)<=>![X11]:(r2_hidden(X11,X10)<=>~(((((((((X11!=X1&X11!=X2)&X11!=X3)&X11!=X4)&X11!=X5)&X11!=X6)&X11!=X7)&X11!=X8)&X11!=X9)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_enumset1)).
% 0.20/0.38  fof(c_0_13, plain, ![X14, X15]:k2_xboole_0(X14,X15)=k5_xboole_0(X14,k4_xboole_0(X15,X14)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.20/0.38  fof(c_0_14, plain, ![X12, X13]:k4_xboole_0(X12,X13)=k5_xboole_0(X12,k3_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.38  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:(k1_tarski(X1)=k2_tarski(X2,X3)=>X1=X2)), inference(assume_negation,[status(cth)],[t8_zfmisc_1])).
% 0.20/0.38  fof(c_0_16, plain, ![X39, X40, X41, X42, X43, X44, X45, X46, X47]:k7_enumset1(X39,X40,X41,X42,X43,X44,X45,X46,X47)=k2_xboole_0(k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46),k1_tarski(X47)), inference(variable_rename,[status(thm)],[t134_enumset1])).
% 0.20/0.38  fof(c_0_17, plain, ![X56]:k2_tarski(X56,X56)=k1_tarski(X56), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.38  fof(c_0_18, plain, ![X57, X58]:k1_enumset1(X57,X57,X58)=k2_tarski(X57,X58), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.38  cnf(c_0_19, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  fof(c_0_21, plain, ![X59, X60, X61]:k2_enumset1(X59,X59,X60,X61)=k1_enumset1(X59,X60,X61), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.38  fof(c_0_22, plain, ![X62, X63, X64, X65]:k3_enumset1(X62,X62,X63,X64,X65)=k2_enumset1(X62,X63,X64,X65), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.38  fof(c_0_23, plain, ![X66, X67, X68, X69, X70]:k4_enumset1(X66,X66,X67,X68,X69,X70)=k3_enumset1(X66,X67,X68,X69,X70), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.38  fof(c_0_24, plain, ![X71, X72, X73, X74, X75, X76]:k5_enumset1(X71,X71,X72,X73,X74,X75,X76)=k4_enumset1(X71,X72,X73,X74,X75,X76), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.38  fof(c_0_25, plain, ![X77, X78, X79, X80, X81, X82, X83]:k6_enumset1(X77,X77,X78,X79,X80,X81,X82,X83)=k5_enumset1(X77,X78,X79,X80,X81,X82,X83), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.20/0.38  fof(c_0_26, negated_conjecture, (k1_tarski(esk2_0)=k2_tarski(esk3_0,esk4_0)&esk2_0!=esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.20/0.38  fof(c_0_27, plain, ![X48, X49, X50, X51, X52, X53, X54, X55]:k6_enumset1(X48,X49,X50,X51,X52,X53,X54,X55)=k2_xboole_0(k5_enumset1(X48,X49,X50,X51,X52,X53,X54),k1_tarski(X55)), inference(variable_rename,[status(thm)],[t68_enumset1])).
% 0.20/0.38  fof(c_0_28, plain, ![X16, X17, X18, X19, X20, X21, X22, X23, X24, X25, X26, X27, X28, X29, X30, X31, X32, X33, X34, X35, X36, X37]:(((~r2_hidden(X26,X25)|(X26=X16|X26=X17|X26=X18|X26=X19|X26=X20|X26=X21|X26=X22|X26=X23|X26=X24)|X25!=k7_enumset1(X16,X17,X18,X19,X20,X21,X22,X23,X24))&(((((((((X27!=X16|r2_hidden(X27,X25)|X25!=k7_enumset1(X16,X17,X18,X19,X20,X21,X22,X23,X24))&(X27!=X17|r2_hidden(X27,X25)|X25!=k7_enumset1(X16,X17,X18,X19,X20,X21,X22,X23,X24)))&(X27!=X18|r2_hidden(X27,X25)|X25!=k7_enumset1(X16,X17,X18,X19,X20,X21,X22,X23,X24)))&(X27!=X19|r2_hidden(X27,X25)|X25!=k7_enumset1(X16,X17,X18,X19,X20,X21,X22,X23,X24)))&(X27!=X20|r2_hidden(X27,X25)|X25!=k7_enumset1(X16,X17,X18,X19,X20,X21,X22,X23,X24)))&(X27!=X21|r2_hidden(X27,X25)|X25!=k7_enumset1(X16,X17,X18,X19,X20,X21,X22,X23,X24)))&(X27!=X22|r2_hidden(X27,X25)|X25!=k7_enumset1(X16,X17,X18,X19,X20,X21,X22,X23,X24)))&(X27!=X23|r2_hidden(X27,X25)|X25!=k7_enumset1(X16,X17,X18,X19,X20,X21,X22,X23,X24)))&(X27!=X24|r2_hidden(X27,X25)|X25!=k7_enumset1(X16,X17,X18,X19,X20,X21,X22,X23,X24))))&((((((((((esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37)!=X28|~r2_hidden(esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37),X37)|X37=k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36))&(esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37)!=X29|~r2_hidden(esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37),X37)|X37=k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36)))&(esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37)!=X30|~r2_hidden(esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37),X37)|X37=k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36)))&(esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37)!=X31|~r2_hidden(esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37),X37)|X37=k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36)))&(esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37)!=X32|~r2_hidden(esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37),X37)|X37=k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36)))&(esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37)!=X33|~r2_hidden(esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37),X37)|X37=k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36)))&(esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37)!=X34|~r2_hidden(esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37),X37)|X37=k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36)))&(esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37)!=X35|~r2_hidden(esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37),X37)|X37=k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36)))&(esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37)!=X36|~r2_hidden(esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37),X37)|X37=k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36)))&(r2_hidden(esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37),X37)|(esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37)=X28|esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37)=X29|esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37)=X30|esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37)=X31|esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37)=X32|esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37)=X33|esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37)=X34|esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37)=X35|esk1_10(X28,X29,X30,X31,X32,X33,X34,X35,X36,X37)=X36)|X37=k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_enumset1])])])])])])).
% 0.20/0.38  cnf(c_0_29, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_30, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_31, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_32, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.38  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.38  cnf(c_0_34, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.38  cnf(c_0_35, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_36, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_37, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (k1_tarski(esk2_0)=k2_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_39, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.38  cnf(c_0_40, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k7_enumset1(X4,X5,X6,X7,X8,X9,X2,X10,X11)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.38  cnf(c_0_41, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k5_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k3_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_30]), c_0_31]), c_0_31]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 0.20/0.38  cnf(c_0_43, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 0.20/0.38  cnf(c_0_44, plain, (r2_hidden(X1,X2)|X2!=k7_enumset1(X3,X4,X5,X6,X7,X8,X1,X9,X10)), inference(er,[status(thm)],[c_0_40])).
% 0.20/0.38  cnf(c_0_45, negated_conjecture, (k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X1)=k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.20/0.38  cnf(c_0_46, plain, (k7_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8)=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(rw,[status(thm)],[c_0_43, c_0_41])).
% 0.20/0.38  cnf(c_0_47, plain, (X1=X3|X1=X4|X1=X5|X1=X6|X1=X7|X1=X8|X1=X9|X1=X10|X1=X11|~r2_hidden(X1,X2)|X2!=k7_enumset1(X3,X4,X5,X6,X7,X8,X9,X10,X11)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.38  cnf(c_0_48, plain, (r2_hidden(X1,k7_enumset1(X2,X3,X4,X5,X6,X7,X1,X8,X9))), inference(er,[status(thm)],[c_0_44])).
% 0.20/0.38  cnf(c_0_49, negated_conjecture, (k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,X1)=k7_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X1)), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.38  cnf(c_0_50, plain, (X1=X2|X1=X3|X1=X4|X1=X5|X1=X6|X1=X7|X1=X8|X1=X9|X1=X10|~r2_hidden(X1,k7_enumset1(X10,X9,X8,X7,X6,X5,X4,X3,X2))), inference(er,[status(thm)],[c_0_47])).
% 0.20/0.38  cnf(c_0_51, negated_conjecture, (r2_hidden(esk3_0,k7_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X1))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.38  cnf(c_0_52, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_53, negated_conjecture, (esk3_0=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.20/0.38  cnf(c_0_54, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_52, c_0_53]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 55
% 0.20/0.38  # Proof object clause steps            : 28
% 0.20/0.38  # Proof object formula steps           : 27
% 0.20/0.38  # Proof object conjectures             : 11
% 0.20/0.38  # Proof object clause conjectures      : 8
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 15
% 0.20/0.38  # Proof object initial formulas used   : 13
% 0.20/0.38  # Proof object generating inferences   : 5
% 0.20/0.38  # Proof object simplifying inferences  : 48
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 13
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 33
% 0.20/0.38  # Removed in clause preprocessing      : 9
% 0.20/0.38  # Initial clauses in saturation        : 24
% 0.20/0.38  # Processed clauses                    : 62
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 5
% 0.20/0.38  # ...remaining for further processing  : 57
% 0.20/0.38  # Other redundant clauses eliminated   : 9
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 46
% 0.20/0.38  # Generated clauses                    : 122
% 0.20/0.38  # ...of the previous two non-trivial   : 142
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 92
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 29
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
% 0.20/0.38  # Current number of processed clauses  : 1
% 0.20/0.38  #    Positive orientable unit clauses  : 0
% 0.20/0.38  #    Positive unorientable unit clauses: 1
% 0.20/0.38  #    Negative unit clauses             : 0
% 0.20/0.38  #    Non-unit-clauses                  : 0
% 0.20/0.38  # Current number of unprocessed clauses: 61
% 0.20/0.38  # ...number of literals in the above   : 210
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 56
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 330
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 329
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 5
% 0.20/0.38  # Unit Clause-clause subsumption calls : 4
% 0.20/0.38  # Rewrite failures with RHS unbound    : 3
% 0.20/0.38  # BW rewrite match attempts            : 68
% 0.20/0.38  # BW rewrite match successes           : 48
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 3275
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.031 s
% 0.20/0.38  # System time              : 0.005 s
% 0.20/0.38  # Total time               : 0.035 s
% 0.20/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
