%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:37:22 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 248 expanded)
%              Number of clauses        :   35 (  96 expanded)
%              Number of leaves         :   18 (  75 expanded)
%              Depth                    :   10
%              Number of atoms          :  182 ( 361 expanded)
%              Number of equality atoms :  148 ( 327 expanded)
%              Maximal formula depth    :   52 (   4 average)
%              Maximal clause size      :   76 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t13_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

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

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t134_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_enumset1)).

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

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t13_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X23,X24] : k2_xboole_0(X23,X24) = k5_xboole_0(X23,k4_xboole_0(X24,X23)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_20,plain,(
    ! [X16,X17] : k4_xboole_0(X16,X17) = k5_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_21,plain,(
    ! [X18] : k5_xboole_0(X18,k1_xboole_0) = X18 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_22,plain,(
    ! [X14,X15] : k5_xboole_0(X14,X15) = k5_xboole_0(X15,X14) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_23,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0)) = k1_tarski(esk3_0)
    & esk3_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_24,plain,(
    ! [X64] : k2_tarski(X64,X64) = k1_tarski(X64) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_25,plain,(
    ! [X65,X66] : k1_enumset1(X65,X65,X66) = k2_tarski(X65,X66) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X67,X68,X69] : k2_enumset1(X67,X67,X68,X69) = k1_enumset1(X67,X68,X69) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_29,plain,(
    ! [X70,X71,X72,X73] : k3_enumset1(X70,X70,X71,X72,X73) = k2_enumset1(X70,X71,X72,X73) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_30,plain,(
    ! [X74,X75,X76,X77,X78] : k4_enumset1(X74,X74,X75,X76,X77,X78) = k3_enumset1(X74,X75,X76,X77,X78) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_31,plain,(
    ! [X79,X80,X81,X82,X83,X84] : k5_enumset1(X79,X79,X80,X81,X82,X83,X84) = k4_enumset1(X79,X80,X81,X82,X83,X84) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_32,plain,(
    ! [X85,X86,X87,X88,X89,X90,X91] : k6_enumset1(X85,X85,X86,X87,X88,X89,X90,X91) = k5_enumset1(X85,X86,X87,X88,X89,X90,X91) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_33,plain,(
    ! [X19,X20,X21] : k5_xboole_0(k5_xboole_0(X19,X20),X21) = k5_xboole_0(X19,k5_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_34,plain,(
    ! [X22] : k5_xboole_0(X22,X22) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_35,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_37,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0)) = k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_38,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_41,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_46,plain,(
    ! [X12,X13] : k3_xboole_0(X12,X13) = k3_xboole_0(X13,X12) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_47,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_49,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_50,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_52,plain,(
    ! [X25,X26,X27,X28,X29,X30] :
      ( ( ~ r2_hidden(X27,X26)
        | X27 = X25
        | X26 != k1_tarski(X25) )
      & ( X28 != X25
        | r2_hidden(X28,X26)
        | X26 != k1_tarski(X25) )
      & ( ~ r2_hidden(esk1_2(X29,X30),X30)
        | esk1_2(X29,X30) != X29
        | X30 = k1_tarski(X29) )
      & ( r2_hidden(esk1_2(X29,X30),X30)
        | esk1_2(X29,X30) = X29
        | X30 = k1_tarski(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_53,plain,(
    ! [X55,X56,X57,X58,X59,X60,X61,X62,X63] : k7_enumset1(X55,X56,X57,X58,X59,X60,X61,X62,X63) = k2_xboole_0(k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62),k1_tarski(X63)) ),
    inference(variable_rename,[status(thm)],[t134_enumset1])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_57,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_48])).

fof(c_0_59,plain,(
    ! [X32,X33,X34,X35,X36,X37,X38,X39,X40,X41,X42,X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53] :
      ( ( ~ r2_hidden(X42,X41)
        | X42 = X32
        | X42 = X33
        | X42 = X34
        | X42 = X35
        | X42 = X36
        | X42 = X37
        | X42 = X38
        | X42 = X39
        | X42 = X40
        | X41 != k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40) )
      & ( X43 != X32
        | r2_hidden(X43,X41)
        | X41 != k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40) )
      & ( X43 != X33
        | r2_hidden(X43,X41)
        | X41 != k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40) )
      & ( X43 != X34
        | r2_hidden(X43,X41)
        | X41 != k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40) )
      & ( X43 != X35
        | r2_hidden(X43,X41)
        | X41 != k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40) )
      & ( X43 != X36
        | r2_hidden(X43,X41)
        | X41 != k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40) )
      & ( X43 != X37
        | r2_hidden(X43,X41)
        | X41 != k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40) )
      & ( X43 != X38
        | r2_hidden(X43,X41)
        | X41 != k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40) )
      & ( X43 != X39
        | r2_hidden(X43,X41)
        | X41 != k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40) )
      & ( X43 != X40
        | r2_hidden(X43,X41)
        | X41 != k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40) )
      & ( esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) != X44
        | ~ r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | X53 = k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) != X45
        | ~ r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | X53 = k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) != X46
        | ~ r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | X53 = k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) != X47
        | ~ r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | X53 = k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) != X48
        | ~ r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | X53 = k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) != X49
        | ~ r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | X53 = k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) != X50
        | ~ r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | X53 = k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) != X51
        | ~ r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | X53 = k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) != X52
        | ~ r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | X53 = k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) = X44
        | esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) = X45
        | esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) = X46
        | esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) = X47
        | esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) = X48
        | esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) = X49
        | esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) = X50
        | esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) = X51
        | esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) = X52
        | X53 = k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_enumset1])])])])])])).

cnf(c_0_60,plain,
    ( X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_38]),c_0_39]),c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45])).

cnf(c_0_61,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k5_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k3_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_45]),c_0_45])).

cnf(c_0_62,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) = k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_58]),c_0_35])).

cnf(c_0_63,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(spm,[status(thm)],[c_0_54,c_0_36])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k7_enumset1(X4,X5,X6,X7,X8,X9,X10,X2,X11) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_65,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,X2)
    | X2 != k7_enumset1(X3,X4,X5,X6,X7,X8,X9,X1,X10) ),
    inference(er,[status(thm)],[c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( X1 = esk3_0
    | ~ r2_hidden(X1,k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,k7_enumset1(X2,X3,X4,X5,X6,X7,X8,X1,X9)) ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:54:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.18/0.34  # No SInE strategy applied
% 0.18/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.41  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.18/0.41  # and selection function SelectNegativeLiterals.
% 0.18/0.41  #
% 0.18/0.41  # Preprocessing time       : 0.029 s
% 0.18/0.41  
% 0.18/0.41  # Proof found!
% 0.18/0.41  # SZS status Theorem
% 0.18/0.41  # SZS output start CNFRefutation
% 0.18/0.41  fof(t13_zfmisc_1, conjecture, ![X1, X2]:(k2_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 0.18/0.41  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.18/0.41  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.18/0.41  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.18/0.41  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.18/0.41  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.18/0.41  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.18/0.41  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.18/0.41  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.18/0.41  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.18/0.41  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.18/0.41  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.18/0.41  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.18/0.41  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.18/0.41  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.18/0.41  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.18/0.41  fof(t134_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_enumset1)).
% 0.18/0.41  fof(d7_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9, X10]:(X10=k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)<=>![X11]:(r2_hidden(X11,X10)<=>~(((((((((X11!=X1&X11!=X2)&X11!=X3)&X11!=X4)&X11!=X5)&X11!=X6)&X11!=X7)&X11!=X8)&X11!=X9)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_enumset1)).
% 0.18/0.41  fof(c_0_18, negated_conjecture, ~(![X1, X2]:(k2_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2)), inference(assume_negation,[status(cth)],[t13_zfmisc_1])).
% 0.18/0.41  fof(c_0_19, plain, ![X23, X24]:k2_xboole_0(X23,X24)=k5_xboole_0(X23,k4_xboole_0(X24,X23)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.18/0.41  fof(c_0_20, plain, ![X16, X17]:k4_xboole_0(X16,X17)=k5_xboole_0(X16,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.18/0.41  fof(c_0_21, plain, ![X18]:k5_xboole_0(X18,k1_xboole_0)=X18, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.18/0.41  fof(c_0_22, plain, ![X14, X15]:k5_xboole_0(X14,X15)=k5_xboole_0(X15,X14), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.18/0.41  fof(c_0_23, negated_conjecture, (k2_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0))=k1_tarski(esk3_0)&esk3_0!=esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.18/0.41  fof(c_0_24, plain, ![X64]:k2_tarski(X64,X64)=k1_tarski(X64), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.18/0.41  fof(c_0_25, plain, ![X65, X66]:k1_enumset1(X65,X65,X66)=k2_tarski(X65,X66), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.18/0.41  cnf(c_0_26, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.41  cnf(c_0_27, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.41  fof(c_0_28, plain, ![X67, X68, X69]:k2_enumset1(X67,X67,X68,X69)=k1_enumset1(X67,X68,X69), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.18/0.41  fof(c_0_29, plain, ![X70, X71, X72, X73]:k3_enumset1(X70,X70,X71,X72,X73)=k2_enumset1(X70,X71,X72,X73), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.18/0.41  fof(c_0_30, plain, ![X74, X75, X76, X77, X78]:k4_enumset1(X74,X74,X75,X76,X77,X78)=k3_enumset1(X74,X75,X76,X77,X78), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.18/0.41  fof(c_0_31, plain, ![X79, X80, X81, X82, X83, X84]:k5_enumset1(X79,X79,X80,X81,X82,X83,X84)=k4_enumset1(X79,X80,X81,X82,X83,X84), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.18/0.41  fof(c_0_32, plain, ![X85, X86, X87, X88, X89, X90, X91]:k6_enumset1(X85,X85,X86,X87,X88,X89,X90,X91)=k5_enumset1(X85,X86,X87,X88,X89,X90,X91), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.18/0.41  fof(c_0_33, plain, ![X19, X20, X21]:k5_xboole_0(k5_xboole_0(X19,X20),X21)=k5_xboole_0(X19,k5_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.18/0.41  fof(c_0_34, plain, ![X22]:k5_xboole_0(X22,X22)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.18/0.41  cnf(c_0_35, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.41  cnf(c_0_36, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.41  cnf(c_0_37, negated_conjecture, (k2_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0))=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.41  cnf(c_0_38, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.41  cnf(c_0_39, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.41  cnf(c_0_40, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.18/0.41  cnf(c_0_41, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.41  cnf(c_0_42, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.41  cnf(c_0_43, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.41  cnf(c_0_44, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.41  cnf(c_0_45, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.41  fof(c_0_46, plain, ![X12, X13]:k3_xboole_0(X12,X13)=k3_xboole_0(X13,X12), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.18/0.41  cnf(c_0_47, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.41  cnf(c_0_48, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.41  cnf(c_0_49, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.18/0.41  cnf(c_0_50, negated_conjecture, (k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45])).
% 0.18/0.41  cnf(c_0_51, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.18/0.41  fof(c_0_52, plain, ![X25, X26, X27, X28, X29, X30]:(((~r2_hidden(X27,X26)|X27=X25|X26!=k1_tarski(X25))&(X28!=X25|r2_hidden(X28,X26)|X26!=k1_tarski(X25)))&((~r2_hidden(esk1_2(X29,X30),X30)|esk1_2(X29,X30)!=X29|X30=k1_tarski(X29))&(r2_hidden(esk1_2(X29,X30),X30)|esk1_2(X29,X30)=X29|X30=k1_tarski(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.18/0.41  fof(c_0_53, plain, ![X55, X56, X57, X58, X59, X60, X61, X62, X63]:k7_enumset1(X55,X56,X57,X58,X59,X60,X61,X62,X63)=k2_xboole_0(k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62),k1_tarski(X63)), inference(variable_rename,[status(thm)],[t134_enumset1])).
% 0.18/0.41  cnf(c_0_54, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 0.18/0.41  cnf(c_0_55, negated_conjecture, (k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))))=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[c_0_50, c_0_51])).
% 0.18/0.41  cnf(c_0_56, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.18/0.41  cnf(c_0_57, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.18/0.41  cnf(c_0_58, negated_conjecture, (k5_xboole_0(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_48])).
% 0.18/0.41  fof(c_0_59, plain, ![X32, X33, X34, X35, X36, X37, X38, X39, X40, X41, X42, X43, X44, X45, X46, X47, X48, X49, X50, X51, X52, X53]:(((~r2_hidden(X42,X41)|(X42=X32|X42=X33|X42=X34|X42=X35|X42=X36|X42=X37|X42=X38|X42=X39|X42=X40)|X41!=k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40))&(((((((((X43!=X32|r2_hidden(X43,X41)|X41!=k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40))&(X43!=X33|r2_hidden(X43,X41)|X41!=k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40)))&(X43!=X34|r2_hidden(X43,X41)|X41!=k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40)))&(X43!=X35|r2_hidden(X43,X41)|X41!=k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40)))&(X43!=X36|r2_hidden(X43,X41)|X41!=k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40)))&(X43!=X37|r2_hidden(X43,X41)|X41!=k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40)))&(X43!=X38|r2_hidden(X43,X41)|X41!=k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40)))&(X43!=X39|r2_hidden(X43,X41)|X41!=k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40)))&(X43!=X40|r2_hidden(X43,X41)|X41!=k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40))))&((((((((((esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)!=X44|~r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|X53=k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52))&(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)!=X45|~r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|X53=k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)!=X46|~r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|X53=k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)!=X47|~r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|X53=k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)!=X48|~r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|X53=k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)!=X49|~r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|X53=k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)!=X50|~r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|X53=k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)!=X51|~r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|X53=k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)!=X52|~r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|X53=k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)=X44|esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)=X45|esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)=X46|esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)=X47|esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)=X48|esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)=X49|esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)=X50|esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)=X51|esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)=X52)|X53=k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_enumset1])])])])])])).
% 0.18/0.41  cnf(c_0_60, plain, (X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_38]), c_0_39]), c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45])).
% 0.18/0.41  cnf(c_0_61, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k5_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k3_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_45]), c_0_45])).
% 0.18/0.41  cnf(c_0_62, negated_conjecture, (k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))=k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_58]), c_0_35])).
% 0.18/0.41  cnf(c_0_63, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(spm,[status(thm)],[c_0_54, c_0_36])).
% 0.18/0.41  cnf(c_0_64, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k7_enumset1(X4,X5,X6,X7,X8,X9,X10,X2,X11)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.18/0.41  cnf(c_0_65, plain, (X1=X2|~r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_60])).
% 0.18/0.41  cnf(c_0_66, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])).
% 0.18/0.41  cnf(c_0_67, plain, (r2_hidden(X1,X2)|X2!=k7_enumset1(X3,X4,X5,X6,X7,X8,X9,X1,X10)), inference(er,[status(thm)],[c_0_64])).
% 0.18/0.41  cnf(c_0_68, negated_conjecture, (X1=esk3_0|~r2_hidden(X1,k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.18/0.41  cnf(c_0_69, plain, (r2_hidden(X1,k7_enumset1(X2,X3,X4,X5,X6,X7,X8,X1,X9))), inference(er,[status(thm)],[c_0_67])).
% 0.18/0.41  cnf(c_0_70, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.41  cnf(c_0_71, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), ['proof']).
% 0.18/0.41  # SZS output end CNFRefutation
% 0.18/0.41  # Proof object total steps             : 72
% 0.18/0.41  # Proof object clause steps            : 35
% 0.18/0.41  # Proof object formula steps           : 37
% 0.18/0.41  # Proof object conjectures             : 12
% 0.18/0.41  # Proof object clause conjectures      : 9
% 0.18/0.41  # Proof object formula conjectures     : 3
% 0.18/0.41  # Proof object initial clauses used    : 19
% 0.18/0.41  # Proof object initial formulas used   : 18
% 0.18/0.41  # Proof object generating inferences   : 10
% 0.18/0.41  # Proof object simplifying inferences  : 60
% 0.18/0.41  # Training examples: 0 positive, 0 negative
% 0.18/0.41  # Parsed axioms                        : 18
% 0.18/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.41  # Initial clauses                      : 41
% 0.18/0.41  # Removed in clause preprocessing      : 9
% 0.18/0.41  # Initial clauses in saturation        : 32
% 0.18/0.41  # Processed clauses                    : 250
% 0.18/0.41  # ...of these trivial                  : 21
% 0.18/0.41  # ...subsumed                          : 151
% 0.18/0.41  # ...remaining for further processing  : 78
% 0.18/0.41  # Other redundant clauses eliminated   : 88
% 0.18/0.41  # Clauses deleted for lack of memory   : 0
% 0.18/0.41  # Backward-subsumed                    : 1
% 0.18/0.41  # Backward-rewritten                   : 4
% 0.18/0.41  # Generated clauses                    : 1714
% 0.18/0.41  # ...of the previous two non-trivial   : 1459
% 0.18/0.41  # Contextual simplify-reflections      : 0
% 0.18/0.41  # Paramodulations                      : 1600
% 0.18/0.41  # Factorizations                       : 8
% 0.18/0.41  # Equation resolutions                 : 106
% 0.18/0.41  # Propositional unsat checks           : 0
% 0.18/0.41  #    Propositional check models        : 0
% 0.18/0.41  #    Propositional check unsatisfiable : 0
% 0.18/0.41  #    Propositional clauses             : 0
% 0.18/0.41  #    Propositional clauses after purity: 0
% 0.18/0.41  #    Propositional unsat core size     : 0
% 0.18/0.41  #    Propositional preprocessing time  : 0.000
% 0.18/0.41  #    Propositional encoding time       : 0.000
% 0.18/0.41  #    Propositional solver time         : 0.000
% 0.18/0.41  #    Success case prop preproc time    : 0.000
% 0.18/0.41  #    Success case prop encoding time   : 0.000
% 0.18/0.41  #    Success case prop solver time     : 0.000
% 0.18/0.41  # Current number of processed clauses  : 63
% 0.18/0.41  #    Positive orientable unit clauses  : 16
% 0.18/0.41  #    Positive unorientable unit clauses: 5
% 0.18/0.41  #    Negative unit clauses             : 1
% 0.18/0.41  #    Non-unit-clauses                  : 41
% 0.18/0.41  # Current number of unprocessed clauses: 1224
% 0.18/0.41  # ...number of literals in the above   : 6029
% 0.18/0.41  # Current number of archived formulas  : 0
% 0.18/0.41  # Current number of archived clauses   : 14
% 0.18/0.41  # Clause-clause subsumption calls (NU) : 280
% 0.18/0.41  # Rec. Clause-clause subsumption calls : 245
% 0.18/0.41  # Non-unit clause-clause subsumptions  : 13
% 0.18/0.41  # Unit Clause-clause subsumption calls : 25
% 0.18/0.41  # Rewrite failures with RHS unbound    : 0
% 0.18/0.41  # BW rewrite match attempts            : 77
% 0.18/0.41  # BW rewrite match successes           : 56
% 0.18/0.41  # Condensation attempts                : 0
% 0.18/0.41  # Condensation successes               : 0
% 0.18/0.41  # Termbank termtop insertions          : 25676
% 0.18/0.41  
% 0.18/0.41  # -------------------------------------------------
% 0.18/0.41  # User time                : 0.069 s
% 0.18/0.41  # System time              : 0.005 s
% 0.18/0.41  # Total time               : 0.074 s
% 0.18/0.41  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
