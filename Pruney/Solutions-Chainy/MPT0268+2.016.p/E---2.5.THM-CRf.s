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
% DateTime   : Thu Dec  3 10:42:19 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 501 expanded)
%              Number of clauses        :   40 ( 224 expanded)
%              Number of leaves         :   14 ( 136 expanded)
%              Depth                    :   13
%              Number of atoms          :  167 ( 928 expanded)
%              Number of equality atoms :   76 ( 567 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

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

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t65_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(c_0_14,plain,(
    ! [X27,X28] : r1_xboole_0(k4_xboole_0(X27,X28),X28) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_15,plain,(
    ! [X23,X24] : k4_xboole_0(X23,X24) = k5_xboole_0(X23,k3_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_16,plain,(
    ! [X26] : k4_xboole_0(k1_xboole_0,X26) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_17,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X31,X32,X33,X34,X35,X36,X37,X38,X39,X40] :
      ( ( ~ r2_hidden(X35,X34)
        | X35 = X31
        | X35 = X32
        | X35 = X33
        | X34 != k1_enumset1(X31,X32,X33) )
      & ( X36 != X31
        | r2_hidden(X36,X34)
        | X34 != k1_enumset1(X31,X32,X33) )
      & ( X36 != X32
        | r2_hidden(X36,X34)
        | X34 != k1_enumset1(X31,X32,X33) )
      & ( X36 != X33
        | r2_hidden(X36,X34)
        | X34 != k1_enumset1(X31,X32,X33) )
      & ( esk3_4(X37,X38,X39,X40) != X37
        | ~ r2_hidden(esk3_4(X37,X38,X39,X40),X40)
        | X40 = k1_enumset1(X37,X38,X39) )
      & ( esk3_4(X37,X38,X39,X40) != X38
        | ~ r2_hidden(esk3_4(X37,X38,X39,X40),X40)
        | X40 = k1_enumset1(X37,X38,X39) )
      & ( esk3_4(X37,X38,X39,X40) != X39
        | ~ r2_hidden(esk3_4(X37,X38,X39,X40),X40)
        | X40 = k1_enumset1(X37,X38,X39) )
      & ( r2_hidden(esk3_4(X37,X38,X39,X40),X40)
        | esk3_4(X37,X38,X39,X40) = X37
        | esk3_4(X37,X38,X39,X40) = X38
        | esk3_4(X37,X38,X39,X40) = X39
        | X40 = k1_enumset1(X37,X38,X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_21,plain,(
    ! [X45,X46,X47] : k2_enumset1(X45,X45,X46,X47) = k1_enumset1(X45,X46,X47) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_22,plain,(
    ! [X48,X49,X50,X51] : k3_enumset1(X48,X48,X49,X50,X51) = k2_enumset1(X48,X49,X50,X51) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_23,plain,(
    ! [X17,X18,X20,X21,X22] :
      ( ( r2_hidden(esk2_2(X17,X18),X17)
        | r1_xboole_0(X17,X18) )
      & ( r2_hidden(esk2_2(X17,X18),X18)
        | r1_xboole_0(X17,X18) )
      & ( ~ r2_hidden(X22,X20)
        | ~ r2_hidden(X22,X21)
        | ~ r1_xboole_0(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_24,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X29,X30] : k2_xboole_0(X29,X30) = k5_xboole_0(X29,k4_xboole_0(X30,X29)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_30,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(X1,k1_tarski(X2)) = X1
      <=> ~ r2_hidden(X2,X1) ) ),
    inference(assume_negation,[status(cth)],[t65_zfmisc_1])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

fof(c_0_34,plain,(
    ! [X25] : k2_xboole_0(X25,k1_xboole_0) = X25 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_36,plain,(
    ! [X52,X53] :
      ( r2_hidden(X52,X53)
      | r1_xboole_0(k1_tarski(X52),X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

fof(c_0_37,plain,(
    ! [X42] : k2_tarski(X42,X42) = k1_tarski(X42) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_38,plain,(
    ! [X43,X44] : k1_enumset1(X43,X43,X44) = k2_tarski(X43,X44) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_39,negated_conjecture,
    ( ( k4_xboole_0(esk4_0,k1_tarski(esk5_0)) != esk4_0
      | r2_hidden(esk5_0,esk4_0) )
    & ( k4_xboole_0(esk4_0,k1_tarski(esk5_0)) = esk4_0
      | ~ r2_hidden(esk5_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_30])])])])).

fof(c_0_40,plain,(
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

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_33])])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_35,c_0_18])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | k4_xboole_0(esk4_0,k1_tarski(esk5_0)) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))) = X1 ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_27]),c_0_28])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) != esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_46]),c_0_47]),c_0_18]),c_0_27]),c_0_28])).

cnf(c_0_54,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk1_3(X1,X2,k1_xboole_0),X2) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_49]),c_0_25]),c_0_25]),c_0_25]),c_0_50])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_51,c_0_25])).

cnf(c_0_56,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X3,k3_enumset1(X1,X1,X1,X1,X1))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k1_xboole_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | r2_hidden(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])])).

cnf(c_0_59,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_56]),c_0_25]),c_0_25]),c_0_25]),c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( k4_xboole_0(esk4_0,k1_tarski(esk5_0)) = esk4_0
    | ~ r2_hidden(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | r2_hidden(esk5_0,X1)
    | ~ r2_hidden(esk1_3(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k1_xboole_0),esk4_0)
    | r2_hidden(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_59]),c_0_55])])).

cnf(c_0_63,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) = esk4_0
    | ~ r2_hidden(esk5_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_46]),c_0_47]),c_0_18]),c_0_27]),c_0_28])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_65,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_24])).

cnf(c_0_66,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64])])).

cnf(c_0_67,negated_conjecture,
    ( ~ r2_hidden(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_42]),c_0_64])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:08:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.12/0.38  # and selection function SelectNegativeLiterals.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.036 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.12/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.12/0.38  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.12/0.38  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.12/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.12/0.38  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.12/0.38  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.12/0.38  fof(t65_zfmisc_1, conjecture, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.12/0.38  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.12/0.38  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.12/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.38  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.12/0.38  fof(c_0_14, plain, ![X27, X28]:r1_xboole_0(k4_xboole_0(X27,X28),X28), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.12/0.38  fof(c_0_15, plain, ![X23, X24]:k4_xboole_0(X23,X24)=k5_xboole_0(X23,k3_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.12/0.38  fof(c_0_16, plain, ![X26]:k4_xboole_0(k1_xboole_0,X26)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.12/0.38  cnf(c_0_17, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.38  cnf(c_0_18, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.38  cnf(c_0_19, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  fof(c_0_20, plain, ![X31, X32, X33, X34, X35, X36, X37, X38, X39, X40]:(((~r2_hidden(X35,X34)|(X35=X31|X35=X32|X35=X33)|X34!=k1_enumset1(X31,X32,X33))&(((X36!=X31|r2_hidden(X36,X34)|X34!=k1_enumset1(X31,X32,X33))&(X36!=X32|r2_hidden(X36,X34)|X34!=k1_enumset1(X31,X32,X33)))&(X36!=X33|r2_hidden(X36,X34)|X34!=k1_enumset1(X31,X32,X33))))&((((esk3_4(X37,X38,X39,X40)!=X37|~r2_hidden(esk3_4(X37,X38,X39,X40),X40)|X40=k1_enumset1(X37,X38,X39))&(esk3_4(X37,X38,X39,X40)!=X38|~r2_hidden(esk3_4(X37,X38,X39,X40),X40)|X40=k1_enumset1(X37,X38,X39)))&(esk3_4(X37,X38,X39,X40)!=X39|~r2_hidden(esk3_4(X37,X38,X39,X40),X40)|X40=k1_enumset1(X37,X38,X39)))&(r2_hidden(esk3_4(X37,X38,X39,X40),X40)|(esk3_4(X37,X38,X39,X40)=X37|esk3_4(X37,X38,X39,X40)=X38|esk3_4(X37,X38,X39,X40)=X39)|X40=k1_enumset1(X37,X38,X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.12/0.38  fof(c_0_21, plain, ![X45, X46, X47]:k2_enumset1(X45,X45,X46,X47)=k1_enumset1(X45,X46,X47), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.38  fof(c_0_22, plain, ![X48, X49, X50, X51]:k3_enumset1(X48,X48,X49,X50,X51)=k2_enumset1(X48,X49,X50,X51), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.12/0.38  fof(c_0_23, plain, ![X17, X18, X20, X21, X22]:(((r2_hidden(esk2_2(X17,X18),X17)|r1_xboole_0(X17,X18))&(r2_hidden(esk2_2(X17,X18),X18)|r1_xboole_0(X17,X18)))&(~r2_hidden(X22,X20)|~r2_hidden(X22,X21)|~r1_xboole_0(X20,X21))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.12/0.38  cnf(c_0_24, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.12/0.38  cnf(c_0_25, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_19, c_0_18])).
% 0.12/0.38  cnf(c_0_26, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.38  cnf(c_0_27, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.38  cnf(c_0_28, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  fof(c_0_29, plain, ![X29, X30]:k2_xboole_0(X29,X30)=k5_xboole_0(X29,k4_xboole_0(X30,X29)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.12/0.38  fof(c_0_30, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1)))), inference(assume_negation,[status(cth)],[t65_zfmisc_1])).
% 0.12/0.38  cnf(c_0_31, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.38  cnf(c_0_32, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.12/0.38  cnf(c_0_33, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.12/0.38  fof(c_0_34, plain, ![X25]:k2_xboole_0(X25,k1_xboole_0)=X25, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.12/0.38  cnf(c_0_35, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.38  fof(c_0_36, plain, ![X52, X53]:(r2_hidden(X52,X53)|r1_xboole_0(k1_tarski(X52),X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.12/0.38  fof(c_0_37, plain, ![X42]:k2_tarski(X42,X42)=k1_tarski(X42), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.38  fof(c_0_38, plain, ![X43, X44]:k1_enumset1(X43,X43,X44)=k2_tarski(X43,X44), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.38  fof(c_0_39, negated_conjecture, ((k4_xboole_0(esk4_0,k1_tarski(esk5_0))!=esk4_0|r2_hidden(esk5_0,esk4_0))&(k4_xboole_0(esk4_0,k1_tarski(esk5_0))=esk4_0|~r2_hidden(esk5_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_30])])])])).
% 0.12/0.38  fof(c_0_40, plain, ![X8, X9, X10, X11, X12, X13, X14, X15]:((((r2_hidden(X11,X8)|~r2_hidden(X11,X10)|X10!=k3_xboole_0(X8,X9))&(r2_hidden(X11,X9)|~r2_hidden(X11,X10)|X10!=k3_xboole_0(X8,X9)))&(~r2_hidden(X12,X8)|~r2_hidden(X12,X9)|r2_hidden(X12,X10)|X10!=k3_xboole_0(X8,X9)))&((~r2_hidden(esk1_3(X13,X14,X15),X15)|(~r2_hidden(esk1_3(X13,X14,X15),X13)|~r2_hidden(esk1_3(X13,X14,X15),X14))|X15=k3_xboole_0(X13,X14))&((r2_hidden(esk1_3(X13,X14,X15),X13)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k3_xboole_0(X13,X14))&(r2_hidden(esk1_3(X13,X14,X15),X14)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k3_xboole_0(X13,X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.12/0.38  cnf(c_0_41, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.12/0.38  cnf(c_0_42, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_33])])).
% 0.12/0.38  cnf(c_0_43, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.38  cnf(c_0_44, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_35, c_0_18])).
% 0.12/0.38  cnf(c_0_45, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.38  cnf(c_0_46, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.12/0.38  cnf(c_0_47, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.12/0.38  cnf(c_0_48, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|k4_xboole_0(esk4_0,k1_tarski(esk5_0))!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.38  cnf(c_0_49, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.12/0.38  cnf(c_0_50, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.12/0.38  cnf(c_0_51, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)))=X1), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 0.12/0.38  cnf(c_0_52, plain, (r2_hidden(X1,X2)|r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_27]), c_0_28])).
% 0.12/0.38  cnf(c_0_53, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))!=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_46]), c_0_47]), c_0_18]), c_0_27]), c_0_28])).
% 0.12/0.38  cnf(c_0_54, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk1_3(X1,X2,k1_xboole_0),X2)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_49]), c_0_25]), c_0_25]), c_0_25]), c_0_50])).
% 0.12/0.38  cnf(c_0_55, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_51, c_0_25])).
% 0.12/0.38  cnf(c_0_56, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.12/0.38  cnf(c_0_57, plain, (r2_hidden(X1,X2)|~r2_hidden(X3,k3_enumset1(X1,X1,X1,X1,X1))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_31, c_0_52])).
% 0.12/0.38  cnf(c_0_58, negated_conjecture, (r2_hidden(esk1_3(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k1_xboole_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|r2_hidden(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])])).
% 0.12/0.38  cnf(c_0_59, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_56]), c_0_25]), c_0_25]), c_0_25]), c_0_50])).
% 0.12/0.38  cnf(c_0_60, negated_conjecture, (k4_xboole_0(esk4_0,k1_tarski(esk5_0))=esk4_0|~r2_hidden(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.38  cnf(c_0_61, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|r2_hidden(esk5_0,X1)|~r2_hidden(esk1_3(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.12/0.38  cnf(c_0_62, negated_conjecture, (r2_hidden(esk1_3(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k1_xboole_0),esk4_0)|r2_hidden(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_59]), c_0_55])])).
% 0.12/0.38  cnf(c_0_63, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))=esk4_0|~r2_hidden(esk5_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_46]), c_0_47]), c_0_18]), c_0_27]), c_0_28])).
% 0.12/0.38  cnf(c_0_64, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.12/0.38  cnf(c_0_65, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_31, c_0_24])).
% 0.12/0.38  cnf(c_0_66, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64])])).
% 0.12/0.38  cnf(c_0_67, negated_conjecture, (~r2_hidden(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.12/0.38  cnf(c_0_68, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_42]), c_0_64])]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 69
% 0.12/0.38  # Proof object clause steps            : 40
% 0.12/0.38  # Proof object formula steps           : 29
% 0.12/0.38  # Proof object conjectures             : 14
% 0.12/0.38  # Proof object clause conjectures      : 11
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 16
% 0.12/0.38  # Proof object initial formulas used   : 14
% 0.12/0.38  # Proof object generating inferences   : 13
% 0.12/0.38  # Proof object simplifying inferences  : 39
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 15
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 30
% 0.12/0.38  # Removed in clause preprocessing      : 6
% 0.12/0.38  # Initial clauses in saturation        : 24
% 0.12/0.38  # Processed clauses                    : 132
% 0.12/0.38  # ...of these trivial                  : 2
% 0.12/0.38  # ...subsumed                          : 30
% 0.12/0.38  # ...remaining for further processing  : 100
% 0.12/0.38  # Other redundant clauses eliminated   : 12
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 0
% 0.12/0.38  # Backward-rewritten                   : 8
% 0.12/0.38  # Generated clauses                    : 582
% 0.12/0.38  # ...of the previous two non-trivial   : 539
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 573
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 12
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
% 0.12/0.38  # Current number of processed clauses  : 61
% 0.12/0.38  #    Positive orientable unit clauses  : 15
% 0.12/0.38  #    Positive unorientable unit clauses: 1
% 0.12/0.38  #    Negative unit clauses             : 1
% 0.12/0.38  #    Non-unit-clauses                  : 44
% 0.12/0.38  # Current number of unprocessed clauses: 453
% 0.12/0.38  # ...number of literals in the above   : 1095
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 38
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 675
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 606
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 17
% 0.12/0.38  # Unit Clause-clause subsumption calls : 8
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 23
% 0.12/0.38  # BW rewrite match successes           : 15
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 10016
% 0.12/0.39  
% 0.12/0.39  # -------------------------------------------------
% 0.12/0.39  # User time                : 0.046 s
% 0.12/0.39  # System time              : 0.005 s
% 0.12/0.39  # Total time               : 0.051 s
% 0.12/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
