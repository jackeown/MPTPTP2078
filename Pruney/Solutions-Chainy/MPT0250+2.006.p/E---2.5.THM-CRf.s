%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:40:08 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 171 expanded)
%              Number of clauses        :   38 (  71 expanded)
%              Number of leaves         :   17 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :  187 ( 345 expanded)
%              Number of equality atoms :   70 ( 193 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(t45_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)
     => r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_17,plain,(
    ! [X63,X64] : k3_tarski(k2_tarski(X63,X64)) = k2_xboole_0(X63,X64) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X49,X50] : k1_enumset1(X49,X49,X50) = k2_tarski(X49,X50) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X30,X31,X32] :
      ( ( r1_xboole_0(X30,k2_xboole_0(X31,X32))
        | ~ r1_xboole_0(X30,X31)
        | ~ r1_xboole_0(X30,X32) )
      & ( r1_xboole_0(X30,X31)
        | ~ r1_xboole_0(X30,k2_xboole_0(X31,X32)) )
      & ( r1_xboole_0(X30,X32)
        | ~ r1_xboole_0(X30,k2_xboole_0(X31,X32)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_20,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X51,X52,X53] : k2_enumset1(X51,X51,X52,X53) = k1_enumset1(X51,X52,X53) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_23,plain,(
    ! [X54,X55,X56,X57] : k3_enumset1(X54,X54,X55,X56,X57) = k2_enumset1(X54,X55,X56,X57) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_24,plain,(
    ! [X58,X59,X60,X61,X62] : k4_enumset1(X58,X58,X59,X60,X61,X62) = k3_enumset1(X58,X59,X60,X61,X62) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_25,plain,(
    ! [X33,X34] : r1_xboole_0(k4_xboole_0(X33,X34),X34) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_26,plain,(
    ! [X26,X27] : k4_xboole_0(X26,X27) = k5_xboole_0(X26,k3_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_27,plain,(
    ! [X37,X38,X39,X40,X41,X42,X43,X44,X45,X46] :
      ( ( ~ r2_hidden(X41,X40)
        | X41 = X37
        | X41 = X38
        | X41 = X39
        | X40 != k1_enumset1(X37,X38,X39) )
      & ( X42 != X37
        | r2_hidden(X42,X40)
        | X40 != k1_enumset1(X37,X38,X39) )
      & ( X42 != X38
        | r2_hidden(X42,X40)
        | X40 != k1_enumset1(X37,X38,X39) )
      & ( X42 != X39
        | r2_hidden(X42,X40)
        | X40 != k1_enumset1(X37,X38,X39) )
      & ( esk3_4(X43,X44,X45,X46) != X43
        | ~ r2_hidden(esk3_4(X43,X44,X45,X46),X46)
        | X46 = k1_enumset1(X43,X44,X45) )
      & ( esk3_4(X43,X44,X45,X46) != X44
        | ~ r2_hidden(esk3_4(X43,X44,X45,X46),X46)
        | X46 = k1_enumset1(X43,X44,X45) )
      & ( esk3_4(X43,X44,X45,X46) != X45
        | ~ r2_hidden(esk3_4(X43,X44,X45,X46),X46)
        | X46 = k1_enumset1(X43,X44,X45) )
      & ( r2_hidden(esk3_4(X43,X44,X45,X46),X46)
        | esk3_4(X43,X44,X45,X46) = X43
        | esk3_4(X43,X44,X45,X46) = X44
        | esk3_4(X43,X44,X45,X46) = X45
        | X46 = k1_enumset1(X43,X44,X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)
       => r2_hidden(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t45_zfmisc_1])).

cnf(c_0_29,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_37,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(esk4_0),esk5_0),esk5_0)
    & ~ r2_hidden(esk4_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).

fof(c_0_38,plain,(
    ! [X48] : k2_tarski(X48,X48) = k1_tarski(X48) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_39,plain,(
    ! [X35,X36] : k2_tarski(X35,X36) = k2_tarski(X36,X35) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_40,plain,(
    ! [X20,X21,X23,X24,X25] :
      ( ( r2_hidden(esk2_2(X20,X21),X20)
        | r1_xboole_0(X20,X21) )
      & ( r2_hidden(esk2_2(X20,X21),X21)
        | r1_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X25,X23)
        | ~ r2_hidden(X25,X24)
        | ~ r1_xboole_0(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_41,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k3_tarski(k4_enumset1(X3,X3,X3,X3,X3,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_42,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_43,plain,(
    ! [X17,X18,X19] :
      ( ( ~ r2_hidden(X17,X18)
        | ~ r2_hidden(X17,X19)
        | ~ r2_hidden(X17,k5_xboole_0(X18,X19)) )
      & ( r2_hidden(X17,X18)
        | r2_hidden(X17,X19)
        | ~ r2_hidden(X17,k5_xboole_0(X18,X19)) )
      & ( ~ r2_hidden(X17,X18)
        | r2_hidden(X17,X19)
        | r2_hidden(X17,k5_xboole_0(X18,X19)) )
      & ( ~ r2_hidden(X17,X19)
        | r2_hidden(X17,X18)
        | r2_hidden(X17,k5_xboole_0(X18,X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X4,X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(esk4_0),esk5_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X3)))),X3) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k4_enumset1(X2,X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_44])])).

fof(c_0_52,plain,(
    ! [X8,X9,X10,X11,X12,X13,X14,X15] :
      ( ( r2_hidden(X11,X8)
        | ~ r2_hidden(X11,X10)
        | X10 != k3_xboole_0(X8,X9) )
      & ( r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | X10 != k3_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X12,X8)
        | ~ r2_hidden(X12,X9)
        | r2_hidden(X12,X10)
        | X10 != k3_xboole_0(X8,X9) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X13)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X14)
        | X15 = k3_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X13)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k3_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X14)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k3_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_53,plain,(
    ! [X28,X29] :
      ( ~ r1_tarski(X28,X29)
      | k3_xboole_0(X28,X29) = X28 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)),esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_21]),c_0_30]),c_0_31]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_33])).

cnf(c_0_55,plain,
    ( k4_enumset1(X1,X1,X1,X1,X1,X2) = k4_enumset1(X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_21]),c_0_21]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33])).

fof(c_0_56,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k3_tarski(k4_enumset1(X3,X3,X3,X3,X3,X4)))))
    | ~ r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,k5_xboole_0(k4_enumset1(X2,X2,X2,X2,X3,X1),X4))
    | r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k3_tarski(k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))),esk5_0) ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_62,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,k3_xboole_0(k4_enumset1(X2,X2,X2,X2,X3,X1),k3_tarski(k4_enumset1(X4,X4,X4,X4,X4,X5))))
    | ~ r2_hidden(X1,X5) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( k3_xboole_0(esk5_0,k3_tarski(k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))) = k3_tarski(k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,k3_xboole_0(k4_enumset1(X2,X2,X2,X2,X3,X1),k3_tarski(k4_enumset1(X4,X4,X4,X4,X4,k4_enumset1(X5,X5,X5,X5,X6,X1))))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_51])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,k3_tarski(k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,k4_enumset1(X3,X3,X3,X3,X4,X1)))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:02:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 1.55/1.77  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 1.55/1.77  # and selection function SelectNegativeLiterals.
% 1.55/1.77  #
% 1.55/1.77  # Preprocessing time       : 0.029 s
% 1.55/1.77  # Presaturation interreduction done
% 1.55/1.77  
% 1.55/1.77  # Proof found!
% 1.55/1.77  # SZS status Theorem
% 1.55/1.77  # SZS output start CNFRefutation
% 1.55/1.77  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.55/1.77  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.55/1.77  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 1.55/1.77  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.55/1.77  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 1.55/1.77  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 1.55/1.77  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.55/1.77  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.55/1.77  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 1.55/1.77  fof(t45_zfmisc_1, conjecture, ![X1, X2]:(r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 1.55/1.77  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.55/1.77  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.55/1.77  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.55/1.77  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 1.55/1.77  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.55/1.77  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.55/1.77  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.55/1.77  fof(c_0_17, plain, ![X63, X64]:k3_tarski(k2_tarski(X63,X64))=k2_xboole_0(X63,X64), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 1.55/1.77  fof(c_0_18, plain, ![X49, X50]:k1_enumset1(X49,X49,X50)=k2_tarski(X49,X50), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.55/1.77  fof(c_0_19, plain, ![X30, X31, X32]:((r1_xboole_0(X30,k2_xboole_0(X31,X32))|~r1_xboole_0(X30,X31)|~r1_xboole_0(X30,X32))&((r1_xboole_0(X30,X31)|~r1_xboole_0(X30,k2_xboole_0(X31,X32)))&(r1_xboole_0(X30,X32)|~r1_xboole_0(X30,k2_xboole_0(X31,X32))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 1.55/1.77  cnf(c_0_20, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.55/1.77  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.55/1.77  fof(c_0_22, plain, ![X51, X52, X53]:k2_enumset1(X51,X51,X52,X53)=k1_enumset1(X51,X52,X53), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.55/1.77  fof(c_0_23, plain, ![X54, X55, X56, X57]:k3_enumset1(X54,X54,X55,X56,X57)=k2_enumset1(X54,X55,X56,X57), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 1.55/1.77  fof(c_0_24, plain, ![X58, X59, X60, X61, X62]:k4_enumset1(X58,X58,X59,X60,X61,X62)=k3_enumset1(X58,X59,X60,X61,X62), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 1.55/1.77  fof(c_0_25, plain, ![X33, X34]:r1_xboole_0(k4_xboole_0(X33,X34),X34), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 1.55/1.77  fof(c_0_26, plain, ![X26, X27]:k4_xboole_0(X26,X27)=k5_xboole_0(X26,k3_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 1.55/1.77  fof(c_0_27, plain, ![X37, X38, X39, X40, X41, X42, X43, X44, X45, X46]:(((~r2_hidden(X41,X40)|(X41=X37|X41=X38|X41=X39)|X40!=k1_enumset1(X37,X38,X39))&(((X42!=X37|r2_hidden(X42,X40)|X40!=k1_enumset1(X37,X38,X39))&(X42!=X38|r2_hidden(X42,X40)|X40!=k1_enumset1(X37,X38,X39)))&(X42!=X39|r2_hidden(X42,X40)|X40!=k1_enumset1(X37,X38,X39))))&((((esk3_4(X43,X44,X45,X46)!=X43|~r2_hidden(esk3_4(X43,X44,X45,X46),X46)|X46=k1_enumset1(X43,X44,X45))&(esk3_4(X43,X44,X45,X46)!=X44|~r2_hidden(esk3_4(X43,X44,X45,X46),X46)|X46=k1_enumset1(X43,X44,X45)))&(esk3_4(X43,X44,X45,X46)!=X45|~r2_hidden(esk3_4(X43,X44,X45,X46),X46)|X46=k1_enumset1(X43,X44,X45)))&(r2_hidden(esk3_4(X43,X44,X45,X46),X46)|(esk3_4(X43,X44,X45,X46)=X43|esk3_4(X43,X44,X45,X46)=X44|esk3_4(X43,X44,X45,X46)=X45)|X46=k1_enumset1(X43,X44,X45)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 1.55/1.77  fof(c_0_28, negated_conjecture, ~(![X1, X2]:(r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)=>r2_hidden(X1,X2))), inference(assume_negation,[status(cth)],[t45_zfmisc_1])).
% 1.55/1.77  cnf(c_0_29, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.55/1.77  cnf(c_0_30, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 1.55/1.77  cnf(c_0_31, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.55/1.77  cnf(c_0_32, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.55/1.77  cnf(c_0_33, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.55/1.77  cnf(c_0_34, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.55/1.77  cnf(c_0_35, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.55/1.77  cnf(c_0_36, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.55/1.77  fof(c_0_37, negated_conjecture, (r1_tarski(k2_xboole_0(k1_tarski(esk4_0),esk5_0),esk5_0)&~r2_hidden(esk4_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).
% 1.55/1.77  fof(c_0_38, plain, ![X48]:k2_tarski(X48,X48)=k1_tarski(X48), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.55/1.77  fof(c_0_39, plain, ![X35, X36]:k2_tarski(X35,X36)=k2_tarski(X36,X35), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 1.55/1.77  fof(c_0_40, plain, ![X20, X21, X23, X24, X25]:(((r2_hidden(esk2_2(X20,X21),X20)|r1_xboole_0(X20,X21))&(r2_hidden(esk2_2(X20,X21),X21)|r1_xboole_0(X20,X21)))&(~r2_hidden(X25,X23)|~r2_hidden(X25,X24)|~r1_xboole_0(X23,X24))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 1.55/1.77  cnf(c_0_41, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k3_tarski(k4_enumset1(X3,X3,X3,X3,X3,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32]), c_0_33])).
% 1.55/1.77  cnf(c_0_42, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 1.55/1.77  fof(c_0_43, plain, ![X17, X18, X19]:(((~r2_hidden(X17,X18)|~r2_hidden(X17,X19)|~r2_hidden(X17,k5_xboole_0(X18,X19)))&(r2_hidden(X17,X18)|r2_hidden(X17,X19)|~r2_hidden(X17,k5_xboole_0(X18,X19))))&((~r2_hidden(X17,X18)|r2_hidden(X17,X19)|r2_hidden(X17,k5_xboole_0(X18,X19)))&(~r2_hidden(X17,X19)|r2_hidden(X17,X18)|r2_hidden(X17,k5_xboole_0(X18,X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 1.55/1.77  cnf(c_0_44, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X4,X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_31]), c_0_32]), c_0_33])).
% 1.55/1.77  cnf(c_0_45, negated_conjecture, (r1_tarski(k2_xboole_0(k1_tarski(esk4_0),esk5_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 1.55/1.77  cnf(c_0_46, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 1.55/1.77  cnf(c_0_47, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.55/1.77  cnf(c_0_48, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.55/1.77  cnf(c_0_49, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X3)))),X3)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 1.55/1.77  cnf(c_0_50, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.55/1.77  cnf(c_0_51, plain, (r2_hidden(X1,k4_enumset1(X2,X2,X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_44])])).
% 1.55/1.77  fof(c_0_52, plain, ![X8, X9, X10, X11, X12, X13, X14, X15]:((((r2_hidden(X11,X8)|~r2_hidden(X11,X10)|X10!=k3_xboole_0(X8,X9))&(r2_hidden(X11,X9)|~r2_hidden(X11,X10)|X10!=k3_xboole_0(X8,X9)))&(~r2_hidden(X12,X8)|~r2_hidden(X12,X9)|r2_hidden(X12,X10)|X10!=k3_xboole_0(X8,X9)))&((~r2_hidden(esk1_3(X13,X14,X15),X15)|(~r2_hidden(esk1_3(X13,X14,X15),X13)|~r2_hidden(esk1_3(X13,X14,X15),X14))|X15=k3_xboole_0(X13,X14))&((r2_hidden(esk1_3(X13,X14,X15),X13)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k3_xboole_0(X13,X14))&(r2_hidden(esk1_3(X13,X14,X15),X14)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k3_xboole_0(X13,X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 1.55/1.77  fof(c_0_53, plain, ![X28, X29]:(~r1_tarski(X28,X29)|k3_xboole_0(X28,X29)=X28), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 1.55/1.77  cnf(c_0_54, negated_conjecture, (r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)),esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_21]), c_0_30]), c_0_31]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_33])).
% 1.55/1.77  cnf(c_0_55, plain, (k4_enumset1(X1,X1,X1,X1,X1,X2)=k4_enumset1(X2,X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_21]), c_0_21]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33])).
% 1.55/1.77  fof(c_0_56, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.55/1.77  cnf(c_0_57, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k3_tarski(k4_enumset1(X3,X3,X3,X3,X3,X4)))))|~r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 1.55/1.77  cnf(c_0_58, plain, (r2_hidden(X1,k5_xboole_0(k4_enumset1(X2,X2,X2,X2,X3,X1),X4))|r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 1.55/1.77  cnf(c_0_59, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 1.55/1.77  cnf(c_0_60, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 1.55/1.77  cnf(c_0_61, negated_conjecture, (r1_tarski(k3_tarski(k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))),esk5_0)), inference(rw,[status(thm)],[c_0_54, c_0_55])).
% 1.55/1.77  cnf(c_0_62, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 1.55/1.77  cnf(c_0_63, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 1.55/1.77  cnf(c_0_64, plain, (r2_hidden(X1,k3_xboole_0(k4_enumset1(X2,X2,X2,X2,X3,X1),k3_tarski(k4_enumset1(X4,X4,X4,X4,X4,X5))))|~r2_hidden(X1,X5)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 1.55/1.77  cnf(c_0_65, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_59])).
% 1.55/1.77  cnf(c_0_66, negated_conjecture, (k3_xboole_0(esk5_0,k3_tarski(k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))))=k3_tarski(k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])).
% 1.55/1.77  cnf(c_0_67, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_63])).
% 1.55/1.77  cnf(c_0_68, plain, (r2_hidden(X1,k3_xboole_0(k4_enumset1(X2,X2,X2,X2,X3,X1),k3_tarski(k4_enumset1(X4,X4,X4,X4,X4,k4_enumset1(X5,X5,X5,X5,X6,X1)))))), inference(spm,[status(thm)],[c_0_64, c_0_51])).
% 1.55/1.77  cnf(c_0_69, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,k3_tarski(k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 1.55/1.77  cnf(c_0_70, plain, (r2_hidden(X1,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,k4_enumset1(X3,X3,X3,X3,X4,X1))))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 1.55/1.77  cnf(c_0_71, negated_conjecture, (~r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 1.55/1.77  cnf(c_0_72, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71]), ['proof']).
% 1.55/1.77  # SZS output end CNFRefutation
% 1.55/1.77  # Proof object total steps             : 73
% 1.55/1.77  # Proof object clause steps            : 38
% 1.55/1.77  # Proof object formula steps           : 35
% 1.55/1.77  # Proof object conjectures             : 10
% 1.55/1.77  # Proof object clause conjectures      : 7
% 1.55/1.77  # Proof object formula conjectures     : 3
% 1.55/1.77  # Proof object initial clauses used    : 19
% 1.55/1.77  # Proof object initial formulas used   : 17
% 1.55/1.77  # Proof object generating inferences   : 9
% 1.55/1.77  # Proof object simplifying inferences  : 39
% 1.55/1.77  # Training examples: 0 positive, 0 negative
% 1.55/1.77  # Parsed axioms                        : 17
% 1.55/1.77  # Removed by relevancy pruning/SinE    : 0
% 1.55/1.77  # Initial clauses                      : 37
% 1.55/1.77  # Removed in clause preprocessing      : 7
% 1.55/1.77  # Initial clauses in saturation        : 30
% 1.55/1.77  # Processed clauses                    : 2669
% 1.55/1.77  # ...of these trivial                  : 104
% 1.55/1.77  # ...subsumed                          : 1450
% 1.55/1.77  # ...remaining for further processing  : 1115
% 1.55/1.77  # Other redundant clauses eliminated   : 118
% 1.55/1.77  # Clauses deleted for lack of memory   : 0
% 1.55/1.77  # Backward-subsumed                    : 12
% 1.55/1.77  # Backward-rewritten                   : 1
% 1.55/1.77  # Generated clauses                    : 116156
% 1.55/1.77  # ...of the previous two non-trivial   : 112714
% 1.55/1.77  # Contextual simplify-reflections      : 0
% 1.55/1.77  # Paramodulations                      : 116017
% 1.55/1.77  # Factorizations                       : 24
% 1.55/1.77  # Equation resolutions                 : 118
% 1.55/1.77  # Propositional unsat checks           : 0
% 1.55/1.77  #    Propositional check models        : 0
% 1.55/1.77  #    Propositional check unsatisfiable : 0
% 1.55/1.77  #    Propositional clauses             : 0
% 1.55/1.77  #    Propositional clauses after purity: 0
% 1.55/1.77  #    Propositional unsat core size     : 0
% 1.55/1.77  #    Propositional preprocessing time  : 0.000
% 1.55/1.77  #    Propositional encoding time       : 0.000
% 1.55/1.77  #    Propositional solver time         : 0.000
% 1.55/1.77  #    Success case prop preproc time    : 0.000
% 1.55/1.77  #    Success case prop encoding time   : 0.000
% 1.55/1.77  #    Success case prop solver time     : 0.000
% 1.55/1.77  # Current number of processed clauses  : 1065
% 1.55/1.77  #    Positive orientable unit clauses  : 82
% 1.55/1.77  #    Positive unorientable unit clauses: 2
% 1.55/1.77  #    Negative unit clauses             : 1
% 1.55/1.77  #    Non-unit-clauses                  : 980
% 1.55/1.77  # Current number of unprocessed clauses: 109587
% 1.55/1.77  # ...number of literals in the above   : 553909
% 1.55/1.77  # Current number of archived formulas  : 0
% 1.55/1.77  # Current number of archived clauses   : 50
% 1.55/1.77  # Clause-clause subsumption calls (NU) : 161877
% 1.55/1.77  # Rec. Clause-clause subsumption calls : 107998
% 1.55/1.77  # Non-unit clause-clause subsumptions  : 1456
% 1.55/1.77  # Unit Clause-clause subsumption calls : 2792
% 1.55/1.77  # Rewrite failures with RHS unbound    : 0
% 1.55/1.77  # BW rewrite match attempts            : 1069
% 1.55/1.77  # BW rewrite match successes           : 18
% 1.55/1.77  # Condensation attempts                : 0
% 1.55/1.77  # Condensation successes               : 0
% 1.55/1.77  # Termbank termtop insertions          : 4523455
% 1.55/1.78  
% 1.55/1.78  # -------------------------------------------------
% 1.55/1.78  # User time                : 1.382 s
% 1.55/1.78  # System time              : 0.055 s
% 1.55/1.78  # Total time               : 1.438 s
% 1.55/1.78  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
