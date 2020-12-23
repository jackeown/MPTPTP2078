%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:40:50 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 589 expanded)
%              Number of clauses        :   39 ( 215 expanded)
%              Number of leaves         :   17 ( 186 expanded)
%              Depth                    :   11
%              Number of atoms          :  145 ( 732 expanded)
%              Number of equality atoms :   77 ( 631 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t47_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X1,X2),X3),X3)
     => r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

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

fof(t113_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X4,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

fof(t55_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t60_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(t60_xboole_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_tarski(X1,X2)
        & r2_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X1,X2),X3),X3)
       => r2_hidden(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t47_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X76,X77] : k3_tarski(k2_tarski(X76,X77)) = k2_xboole_0(X76,X77) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X47,X48] : k1_enumset1(X47,X47,X48) = k2_tarski(X47,X48) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0),esk5_0)
    & ~ r2_hidden(esk3_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_21,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X49,X50,X51] : k2_enumset1(X49,X49,X50,X51) = k1_enumset1(X49,X50,X51) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X52,X53,X54,X55] : k3_enumset1(X52,X52,X53,X54,X55) = k2_enumset1(X52,X53,X54,X55) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_25,plain,(
    ! [X56,X57,X58,X59,X60] : k4_enumset1(X56,X56,X57,X58,X59,X60) = k3_enumset1(X56,X57,X58,X59,X60) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_26,plain,(
    ! [X61,X62,X63,X64,X65,X66] : k5_enumset1(X61,X61,X62,X63,X64,X65,X66) = k4_enumset1(X61,X62,X63,X64,X65,X66) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_27,plain,(
    ! [X67,X68,X69,X70,X71,X72,X73] : k6_enumset1(X67,X67,X68,X69,X70,X71,X72,X73) = k5_enumset1(X67,X68,X69,X70,X71,X72,X73) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_28,plain,(
    ! [X29,X30,X31,X32] : k2_enumset1(X29,X30,X31,X32) = k2_enumset1(X30,X32,X31,X29) ),
    inference(variable_rename,[status(thm)],[t113_enumset1])).

fof(c_0_29,plain,(
    ! [X33,X34,X35,X36,X37,X38] : k4_enumset1(X33,X34,X35,X36,X37,X38) = k2_xboole_0(k3_enumset1(X33,X34,X35,X36,X37),k1_tarski(X38)) ),
    inference(variable_rename,[status(thm)],[t55_enumset1])).

fof(c_0_30,plain,(
    ! [X46] : k2_tarski(X46,X46) = k1_tarski(X46) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_31,plain,(
    ! [X39,X40,X41,X42,X43,X44,X45] : k5_enumset1(X39,X40,X41,X42,X43,X44,X45) = k2_xboole_0(k3_enumset1(X39,X40,X41,X42,X43),k2_tarski(X44,X45)) ),
    inference(variable_rename,[status(thm)],[t60_enumset1])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_34,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X4,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)),esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_22]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38])).

cnf(c_0_44,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X2,X2,X2,X2,X2,X4,X3,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38])).

cnf(c_0_45,plain,
    ( k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_22]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38])).

cnf(c_0_46,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_22]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38])).

fof(c_0_47,plain,(
    ! [X18,X19,X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( ~ r2_hidden(X22,X21)
        | X22 = X18
        | X22 = X19
        | X22 = X20
        | X21 != k1_enumset1(X18,X19,X20) )
      & ( X23 != X18
        | r2_hidden(X23,X21)
        | X21 != k1_enumset1(X18,X19,X20) )
      & ( X23 != X19
        | r2_hidden(X23,X21)
        | X21 != k1_enumset1(X18,X19,X20) )
      & ( X23 != X20
        | r2_hidden(X23,X21)
        | X21 != k1_enumset1(X18,X19,X20) )
      & ( esk2_4(X24,X25,X26,X27) != X24
        | ~ r2_hidden(esk2_4(X24,X25,X26,X27),X27)
        | X27 = k1_enumset1(X24,X25,X26) )
      & ( esk2_4(X24,X25,X26,X27) != X25
        | ~ r2_hidden(esk2_4(X24,X25,X26,X27),X27)
        | X27 = k1_enumset1(X24,X25,X26) )
      & ( esk2_4(X24,X25,X26,X27) != X26
        | ~ r2_hidden(esk2_4(X24,X25,X26,X27),X27)
        | X27 = k1_enumset1(X24,X25,X26) )
      & ( r2_hidden(esk2_4(X24,X25,X26,X27),X27)
        | esk2_4(X24,X25,X26,X27) = X24
        | esk2_4(X24,X25,X26,X27) = X25
        | esk2_4(X24,X25,X26,X27) = X26
        | X27 = k1_enumset1(X24,X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_48,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | ~ r2_xboole_0(X14,X15) )
      & ( X14 != X15
        | ~ r2_xboole_0(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | X14 = X15
        | r2_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),esk5_0) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X6) = k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X2,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_53,plain,(
    ! [X16,X17] :
      ( ~ r1_tarski(X16,X17)
      | ~ r2_xboole_0(X17,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_xboole_1])])).

cnf(c_0_54,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50]),c_0_50])).

fof(c_0_56,plain,(
    ! [X74,X75] :
      ( ~ r2_hidden(X74,X75)
      | r1_tarski(X74,k3_tarski(X75)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X4,X4,X4,X2,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_59,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))) = esk5_0
    | r2_xboole_0(k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_57])])).

fof(c_0_63,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_58])])).

cnf(c_0_65,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))) = esk5_0
    | ~ r1_tarski(esk5_0,k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X3))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_67,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66])])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X1,X4),X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_62])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:51:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.12/0.38  # and selection function GSelectMinInfpos.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.027 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t47_zfmisc_1, conjecture, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(k2_tarski(X1,X2),X3),X3)=>r2_hidden(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 0.12/0.38  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.12/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.12/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.12/0.38  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.12/0.38  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.12/0.38  fof(t113_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X4,X3,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 0.12/0.38  fof(t55_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 0.12/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.38  fof(t60_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_enumset1)).
% 0.12/0.38  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.12/0.38  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.12/0.38  fof(t60_xboole_1, axiom, ![X1, X2]:~((r1_tarski(X1,X2)&r2_xboole_0(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 0.12/0.38  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.12/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.38  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(k2_xboole_0(k2_tarski(X1,X2),X3),X3)=>r2_hidden(X1,X3))), inference(assume_negation,[status(cth)],[t47_zfmisc_1])).
% 0.12/0.38  fof(c_0_18, plain, ![X76, X77]:k3_tarski(k2_tarski(X76,X77))=k2_xboole_0(X76,X77), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.12/0.38  fof(c_0_19, plain, ![X47, X48]:k1_enumset1(X47,X47,X48)=k2_tarski(X47,X48), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.38  fof(c_0_20, negated_conjecture, (r1_tarski(k2_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0),esk5_0)&~r2_hidden(esk3_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.12/0.38  cnf(c_0_21, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.38  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.38  fof(c_0_23, plain, ![X49, X50, X51]:k2_enumset1(X49,X49,X50,X51)=k1_enumset1(X49,X50,X51), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.38  fof(c_0_24, plain, ![X52, X53, X54, X55]:k3_enumset1(X52,X52,X53,X54,X55)=k2_enumset1(X52,X53,X54,X55), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.12/0.38  fof(c_0_25, plain, ![X56, X57, X58, X59, X60]:k4_enumset1(X56,X56,X57,X58,X59,X60)=k3_enumset1(X56,X57,X58,X59,X60), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.12/0.38  fof(c_0_26, plain, ![X61, X62, X63, X64, X65, X66]:k5_enumset1(X61,X61,X62,X63,X64,X65,X66)=k4_enumset1(X61,X62,X63,X64,X65,X66), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.12/0.38  fof(c_0_27, plain, ![X67, X68, X69, X70, X71, X72, X73]:k6_enumset1(X67,X67,X68,X69,X70,X71,X72,X73)=k5_enumset1(X67,X68,X69,X70,X71,X72,X73), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.12/0.38  fof(c_0_28, plain, ![X29, X30, X31, X32]:k2_enumset1(X29,X30,X31,X32)=k2_enumset1(X30,X32,X31,X29), inference(variable_rename,[status(thm)],[t113_enumset1])).
% 0.12/0.38  fof(c_0_29, plain, ![X33, X34, X35, X36, X37, X38]:k4_enumset1(X33,X34,X35,X36,X37,X38)=k2_xboole_0(k3_enumset1(X33,X34,X35,X36,X37),k1_tarski(X38)), inference(variable_rename,[status(thm)],[t55_enumset1])).
% 0.12/0.38  fof(c_0_30, plain, ![X46]:k2_tarski(X46,X46)=k1_tarski(X46), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.38  fof(c_0_31, plain, ![X39, X40, X41, X42, X43, X44, X45]:k5_enumset1(X39,X40,X41,X42,X43,X44,X45)=k2_xboole_0(k3_enumset1(X39,X40,X41,X42,X43),k2_tarski(X44,X45)), inference(variable_rename,[status(thm)],[t60_enumset1])).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, (r1_tarski(k2_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.38  cnf(c_0_33, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.12/0.38  cnf(c_0_34, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.38  cnf(c_0_35, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.38  cnf(c_0_36, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.38  cnf(c_0_37, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.38  cnf(c_0_38, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.38  cnf(c_0_39, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X4,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.38  cnf(c_0_40, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.38  cnf(c_0_41, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.38  cnf(c_0_42, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.38  cnf(c_0_43, negated_conjecture, (r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)),esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_22]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38])).
% 0.12/0.38  cnf(c_0_44, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k6_enumset1(X2,X2,X2,X2,X2,X4,X3,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38])).
% 0.12/0.38  cnf(c_0_45, plain, (k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_22]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38])).
% 0.12/0.38  cnf(c_0_46, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_22]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38])).
% 0.12/0.38  fof(c_0_47, plain, ![X18, X19, X20, X21, X22, X23, X24, X25, X26, X27]:(((~r2_hidden(X22,X21)|(X22=X18|X22=X19|X22=X20)|X21!=k1_enumset1(X18,X19,X20))&(((X23!=X18|r2_hidden(X23,X21)|X21!=k1_enumset1(X18,X19,X20))&(X23!=X19|r2_hidden(X23,X21)|X21!=k1_enumset1(X18,X19,X20)))&(X23!=X20|r2_hidden(X23,X21)|X21!=k1_enumset1(X18,X19,X20))))&((((esk2_4(X24,X25,X26,X27)!=X24|~r2_hidden(esk2_4(X24,X25,X26,X27),X27)|X27=k1_enumset1(X24,X25,X26))&(esk2_4(X24,X25,X26,X27)!=X25|~r2_hidden(esk2_4(X24,X25,X26,X27),X27)|X27=k1_enumset1(X24,X25,X26)))&(esk2_4(X24,X25,X26,X27)!=X26|~r2_hidden(esk2_4(X24,X25,X26,X27),X27)|X27=k1_enumset1(X24,X25,X26)))&(r2_hidden(esk2_4(X24,X25,X26,X27),X27)|(esk2_4(X24,X25,X26,X27)=X24|esk2_4(X24,X25,X26,X27)=X25|esk2_4(X24,X25,X26,X27)=X26)|X27=k1_enumset1(X24,X25,X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.12/0.38  fof(c_0_48, plain, ![X14, X15]:(((r1_tarski(X14,X15)|~r2_xboole_0(X14,X15))&(X14!=X15|~r2_xboole_0(X14,X15)))&(~r1_tarski(X14,X15)|X14=X15|r2_xboole_0(X14,X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.12/0.38  cnf(c_0_49, negated_conjecture, (r1_tarski(k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),esk5_0)), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 0.12/0.38  cnf(c_0_50, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X6)=k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.12/0.38  cnf(c_0_51, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X2,X5)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.12/0.38  cnf(c_0_52, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.12/0.38  fof(c_0_53, plain, ![X16, X17]:(~r1_tarski(X16,X17)|~r2_xboole_0(X17,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_xboole_1])])).
% 0.12/0.38  cnf(c_0_54, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.12/0.38  cnf(c_0_55, negated_conjecture, (r1_tarski(k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50]), c_0_50])).
% 0.12/0.38  fof(c_0_56, plain, ![X74, X75]:(~r2_hidden(X74,X75)|r1_tarski(X74,k3_tarski(X75))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.12/0.38  cnf(c_0_57, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X4,X4,X4,X2,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 0.12/0.38  cnf(c_0_58, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 0.12/0.38  cnf(c_0_59, plain, (~r1_tarski(X1,X2)|~r2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.12/0.38  cnf(c_0_60, negated_conjecture, (k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))=esk5_0|r2_xboole_0(k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),esk5_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.12/0.38  cnf(c_0_61, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.12/0.38  cnf(c_0_62, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_57])])).
% 0.12/0.38  fof(c_0_63, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.38  cnf(c_0_64, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_58])])).
% 0.12/0.38  cnf(c_0_65, negated_conjecture, (k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))=esk5_0|~r1_tarski(esk5_0,k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.12/0.38  cnf(c_0_66, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X3)))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.12/0.38  cnf(c_0_67, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.12/0.38  cnf(c_0_68, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1)))), inference(spm,[status(thm)],[c_0_61, c_0_64])).
% 0.12/0.38  cnf(c_0_69, negated_conjecture, (k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66])])).
% 0.12/0.38  cnf(c_0_70, plain, (r2_hidden(X1,X2)|~r1_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X1,X4),X2)), inference(spm,[status(thm)],[c_0_67, c_0_62])).
% 0.12/0.38  cnf(c_0_71, negated_conjecture, (r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.12/0.38  cnf(c_0_72, negated_conjecture, (~r2_hidden(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.38  cnf(c_0_73, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 74
% 0.12/0.38  # Proof object clause steps            : 39
% 0.12/0.38  # Proof object formula steps           : 35
% 0.12/0.38  # Proof object conjectures             : 13
% 0.12/0.38  # Proof object clause conjectures      : 10
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 19
% 0.12/0.38  # Proof object initial formulas used   : 17
% 0.12/0.38  # Proof object generating inferences   : 7
% 0.12/0.38  # Proof object simplifying inferences  : 115
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 17
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 29
% 0.12/0.38  # Removed in clause preprocessing      : 8
% 0.12/0.38  # Initial clauses in saturation        : 21
% 0.12/0.38  # Processed clauses                    : 110
% 0.12/0.38  # ...of these trivial                  : 0
% 0.12/0.38  # ...subsumed                          : 19
% 0.12/0.38  # ...remaining for further processing  : 91
% 0.12/0.38  # Other redundant clauses eliminated   : 17
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 1
% 0.12/0.38  # Backward-rewritten                   : 11
% 0.12/0.38  # Generated clauses                    : 460
% 0.12/0.38  # ...of the previous two non-trivial   : 411
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 440
% 0.12/0.38  # Factorizations                       : 6
% 0.12/0.38  # Equation resolutions                 : 17
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 53
% 0.12/0.38  #    Positive orientable unit clauses  : 14
% 0.12/0.38  #    Positive unorientable unit clauses: 2
% 0.12/0.38  #    Negative unit clauses             : 2
% 0.12/0.38  #    Non-unit-clauses                  : 35
% 0.12/0.38  # Current number of unprocessed clauses: 340
% 0.12/0.38  # ...number of literals in the above   : 1469
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 41
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 193
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 103
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 20
% 0.12/0.38  # Unit Clause-clause subsumption calls : 76
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 131
% 0.12/0.38  # BW rewrite match successes           : 53
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 11404
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.043 s
% 0.12/0.38  # System time              : 0.004 s
% 0.12/0.38  # Total time               : 0.047 s
% 0.12/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
