%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:57 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 234 expanded)
%              Number of clauses        :   46 ( 103 expanded)
%              Number of leaves         :   16 (  60 expanded)
%              Depth                    :   15
%              Number of atoms          :  145 ( 454 expanded)
%              Number of equality atoms :   34 ( 125 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

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

fof(t149_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
        & r2_hidden(X4,X3)
        & r1_xboole_0(X3,X2) )
     => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t77_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r1_xboole_0(X1,X2)
        & r1_tarski(X1,X3)
        & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(c_0_16,plain,(
    ! [X32,X33] : r1_xboole_0(k4_xboole_0(X32,X33),X33) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_17,plain,(
    ! [X17,X18] : k4_xboole_0(X17,X18) = k5_xboole_0(X17,k3_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_18,plain,(
    ! [X11,X12,X14,X15,X16] :
      ( ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_2(X11,X12),X12)
        | r1_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | ~ r1_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_19,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
          & r2_hidden(X4,X3)
          & r1_xboole_0(X3,X2) )
       => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t149_zfmisc_1])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_24,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0))
    & r2_hidden(esk5_0,esk4_0)
    & r1_xboole_0(esk4_0,esk3_0)
    & ~ r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_27,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_28,plain,(
    ! [X7,X8] :
      ( ( ~ r1_xboole_0(X7,X8)
        | k3_xboole_0(X7,X8) = k1_xboole_0 )
      & ( k3_xboole_0(X7,X8) != k1_xboole_0
        | r1_xboole_0(X7,X8) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_29,plain,(
    ! [X34,X35] :
      ( ( ~ r1_xboole_0(X34,X35)
        | k4_xboole_0(X34,X35) = X34 )
      & ( k4_xboole_0(X34,X35) != X34
        | r1_xboole_0(X34,X35) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_30,plain,(
    ! [X9,X10] :
      ( ~ r1_xboole_0(X9,X10)
      | r1_xboole_0(X10,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k5_xboole_0(X1,k3_xboole_0(X1,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k5_xboole_0(X1,k3_xboole_0(esk4_0,X1))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_20])).

cnf(c_0_40,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_34])).

fof(c_0_41,plain,(
    ! [X42,X43] :
      ( ( k4_xboole_0(X42,k1_tarski(X43)) != X42
        | ~ r2_hidden(X43,X42) )
      & ( r2_hidden(X43,X42)
        | k4_xboole_0(X42,k1_tarski(X43)) = X42 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_42,plain,(
    ! [X36] : k2_tarski(X36,X36) = k1_tarski(X36) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_43,plain,(
    ! [X37,X38] : k1_enumset1(X37,X37,X38) = k2_tarski(X37,X38) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_44,plain,(
    ! [X39,X40,X41] : k2_enumset1(X39,X39,X40,X41) = k1_enumset1(X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_45,plain,(
    ! [X21,X22] : r1_tarski(k4_xboole_0(X21,X22),X21) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_46,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k5_xboole_0(esk3_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_xboole_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_32]),c_0_38])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(X2,k1_tarski(X1)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_53,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_hidden(esk5_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X2,k3_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))) = X2
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_20]),c_0_51])).

fof(c_0_56,plain,(
    ! [X29,X30,X31] :
      ( r1_xboole_0(X29,X30)
      | ~ r1_tarski(X29,X31)
      | ~ r1_xboole_0(X29,k3_xboole_0(X30,X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t77_xboole_1])])])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk2_0,esk3_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_49]),c_0_50]),c_0_51])).

cnf(c_0_58,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_53,c_0_20])).

cnf(c_0_59,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_57,c_0_32])).

cnf(c_0_62,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_23]),c_0_32])).

fof(c_0_63,plain,(
    ! [X25] : r1_xboole_0(X25,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(esk3_0,esk2_0),X1)
    | ~ r1_xboole_0(k3_xboole_0(esk3_0,esk2_0),k3_xboole_0(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( k3_xboole_0(esk3_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_59]),c_0_32])).

cnf(c_0_67,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_68,plain,(
    ! [X26,X27,X28] :
      ( ( r1_xboole_0(X26,k2_xboole_0(X27,X28))
        | ~ r1_xboole_0(X26,X27)
        | ~ r1_xboole_0(X26,X28) )
      & ( r1_xboole_0(X26,X27)
        | ~ r1_xboole_0(X26,k2_xboole_0(X27,X28)) )
      & ( r1_xboole_0(X26,X28)
        | ~ r1_xboole_0(X26,k2_xboole_0(X27,X28)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_69,negated_conjecture,
    ( r1_xboole_0(esk3_0,X1)
    | ~ r1_xboole_0(esk3_0,k3_xboole_0(X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(esk3_0,esk2_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])])).

cnf(c_0_71,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( r1_xboole_0(esk3_0,X1)
    | ~ r1_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_32])).

cnf(c_0_73,negated_conjecture,
    ( r1_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( r1_xboole_0(esk3_0,k2_xboole_0(X1,esk4_0))
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_40])).

cnf(c_0_75,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( r1_xboole_0(esk3_0,k2_xboole_0(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_77,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_76]),c_0_77]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:27:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.20/0.39  # and selection function SelectCQArNTNpEqFirst.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.027 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.20/0.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.39  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.39  fof(t149_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 0.20/0.39  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.39  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.20/0.39  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.20/0.39  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.20/0.39  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.20/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.39  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.20/0.39  fof(t77_xboole_1, axiom, ![X1, X2, X3]:~(((~(r1_xboole_0(X1,X2))&r1_tarski(X1,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 0.20/0.39  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.20/0.39  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.20/0.39  fof(c_0_16, plain, ![X32, X33]:r1_xboole_0(k4_xboole_0(X32,X33),X33), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.20/0.39  fof(c_0_17, plain, ![X17, X18]:k4_xboole_0(X17,X18)=k5_xboole_0(X17,k3_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.39  fof(c_0_18, plain, ![X11, X12, X14, X15, X16]:(((r2_hidden(esk1_2(X11,X12),X11)|r1_xboole_0(X11,X12))&(r2_hidden(esk1_2(X11,X12),X12)|r1_xboole_0(X11,X12)))&(~r2_hidden(X16,X14)|~r2_hidden(X16,X15)|~r1_xboole_0(X14,X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.39  cnf(c_0_19, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  fof(c_0_21, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t149_zfmisc_1])).
% 0.20/0.39  cnf(c_0_22, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_23, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.39  fof(c_0_24, negated_conjecture, (((r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0))&r2_hidden(esk5_0,esk4_0))&r1_xboole_0(esk4_0,esk3_0))&~r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.20/0.39  cnf(c_0_25, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.39  cnf(c_0_26, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  fof(c_0_27, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.39  fof(c_0_28, plain, ![X7, X8]:((~r1_xboole_0(X7,X8)|k3_xboole_0(X7,X8)=k1_xboole_0)&(k3_xboole_0(X7,X8)!=k1_xboole_0|r1_xboole_0(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.20/0.39  fof(c_0_29, plain, ![X34, X35]:((~r1_xboole_0(X34,X35)|k4_xboole_0(X34,X35)=X34)&(k4_xboole_0(X34,X35)!=X34|r1_xboole_0(X34,X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.20/0.39  fof(c_0_30, plain, ![X9, X10]:(~r1_xboole_0(X9,X10)|r1_xboole_0(X10,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.20/0.39  cnf(c_0_31, negated_conjecture, (~r2_hidden(esk5_0,k5_xboole_0(X1,k3_xboole_0(X1,esk4_0)))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.39  cnf(c_0_32, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  cnf(c_0_33, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.39  cnf(c_0_34, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  cnf(c_0_35, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.39  cnf(c_0_36, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.39  cnf(c_0_37, negated_conjecture, (~r2_hidden(esk5_0,k5_xboole_0(X1,k3_xboole_0(esk4_0,X1)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.39  cnf(c_0_38, negated_conjecture, (k3_xboole_0(esk4_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.39  cnf(c_0_39, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_35, c_0_20])).
% 0.20/0.39  cnf(c_0_40, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_36, c_0_34])).
% 0.20/0.39  fof(c_0_41, plain, ![X42, X43]:((k4_xboole_0(X42,k1_tarski(X43))!=X42|~r2_hidden(X43,X42))&(r2_hidden(X43,X42)|k4_xboole_0(X42,k1_tarski(X43))=X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.20/0.39  fof(c_0_42, plain, ![X36]:k2_tarski(X36,X36)=k1_tarski(X36), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.39  fof(c_0_43, plain, ![X37, X38]:k1_enumset1(X37,X37,X38)=k2_tarski(X37,X38), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.39  fof(c_0_44, plain, ![X39, X40, X41]:k2_enumset1(X39,X39,X40,X41)=k1_enumset1(X39,X40,X41), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.39  fof(c_0_45, plain, ![X21, X22]:r1_tarski(k4_xboole_0(X21,X22),X21), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.20/0.39  cnf(c_0_46, negated_conjecture, (~r2_hidden(esk5_0,k5_xboole_0(esk3_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.39  cnf(c_0_47, negated_conjecture, (k5_xboole_0(esk3_0,k1_xboole_0)=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_32]), c_0_38])).
% 0.20/0.39  cnf(c_0_48, plain, (r2_hidden(X1,X2)|k4_xboole_0(X2,k1_tarski(X1))=X2), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.39  cnf(c_0_49, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.39  cnf(c_0_50, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.39  cnf(c_0_51, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.39  cnf(c_0_52, negated_conjecture, (r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  cnf(c_0_53, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.39  cnf(c_0_54, negated_conjecture, (~r2_hidden(esk5_0,esk3_0)), inference(rw,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.39  cnf(c_0_55, plain, (k5_xboole_0(X2,k3_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)))=X2|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_20]), c_0_51])).
% 0.20/0.39  fof(c_0_56, plain, ![X29, X30, X31]:(r1_xboole_0(X29,X30)|~r1_tarski(X29,X31)|~r1_xboole_0(X29,k3_xboole_0(X30,X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t77_xboole_1])])])).
% 0.20/0.39  cnf(c_0_57, negated_conjecture, (r1_tarski(k3_xboole_0(esk2_0,esk3_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_49]), c_0_50]), c_0_51])).
% 0.20/0.39  cnf(c_0_58, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_53, c_0_20])).
% 0.20/0.39  cnf(c_0_59, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))=esk3_0), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.39  cnf(c_0_60, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,X3)|~r1_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.39  cnf(c_0_61, negated_conjecture, (r1_tarski(k3_xboole_0(esk3_0,esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[c_0_57, c_0_32])).
% 0.20/0.39  cnf(c_0_62, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_23]), c_0_32])).
% 0.20/0.39  fof(c_0_63, plain, ![X25]:r1_xboole_0(X25,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.20/0.39  cnf(c_0_64, negated_conjecture, (r1_tarski(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.20/0.39  cnf(c_0_65, negated_conjecture, (r1_xboole_0(k3_xboole_0(esk3_0,esk2_0),X1)|~r1_xboole_0(k3_xboole_0(esk3_0,esk2_0),k3_xboole_0(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.39  cnf(c_0_66, negated_conjecture, (k3_xboole_0(esk3_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_59]), c_0_32])).
% 0.20/0.39  cnf(c_0_67, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.39  fof(c_0_68, plain, ![X26, X27, X28]:((r1_xboole_0(X26,k2_xboole_0(X27,X28))|~r1_xboole_0(X26,X27)|~r1_xboole_0(X26,X28))&((r1_xboole_0(X26,X27)|~r1_xboole_0(X26,k2_xboole_0(X27,X28)))&(r1_xboole_0(X26,X28)|~r1_xboole_0(X26,k2_xboole_0(X27,X28))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.20/0.39  cnf(c_0_69, negated_conjecture, (r1_xboole_0(esk3_0,X1)|~r1_xboole_0(esk3_0,k3_xboole_0(X1,esk3_0))), inference(spm,[status(thm)],[c_0_60, c_0_64])).
% 0.20/0.39  cnf(c_0_70, negated_conjecture, (r1_xboole_0(k3_xboole_0(esk3_0,esk2_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])])).
% 0.20/0.39  cnf(c_0_71, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.39  cnf(c_0_72, negated_conjecture, (r1_xboole_0(esk3_0,X1)|~r1_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1))), inference(spm,[status(thm)],[c_0_69, c_0_32])).
% 0.20/0.39  cnf(c_0_73, negated_conjecture, (r1_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk2_0))), inference(spm,[status(thm)],[c_0_36, c_0_70])).
% 0.20/0.39  cnf(c_0_74, negated_conjecture, (r1_xboole_0(esk3_0,k2_xboole_0(X1,esk4_0))|~r1_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_71, c_0_40])).
% 0.20/0.39  cnf(c_0_75, negated_conjecture, (r1_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.20/0.39  cnf(c_0_76, negated_conjecture, (r1_xboole_0(esk3_0,k2_xboole_0(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.20/0.39  cnf(c_0_77, negated_conjecture, (~r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  cnf(c_0_78, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_76]), c_0_77]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 79
% 0.20/0.39  # Proof object clause steps            : 46
% 0.20/0.39  # Proof object formula steps           : 33
% 0.20/0.39  # Proof object conjectures             : 28
% 0.20/0.39  # Proof object clause conjectures      : 25
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 19
% 0.20/0.39  # Proof object initial formulas used   : 16
% 0.20/0.39  # Proof object generating inferences   : 20
% 0.20/0.39  # Proof object simplifying inferences  : 19
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 18
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 28
% 0.20/0.39  # Removed in clause preprocessing      : 4
% 0.20/0.39  # Initial clauses in saturation        : 24
% 0.20/0.39  # Processed clauses                    : 397
% 0.20/0.39  # ...of these trivial                  : 48
% 0.20/0.39  # ...subsumed                          : 92
% 0.20/0.39  # ...remaining for further processing  : 257
% 0.20/0.39  # Other redundant clauses eliminated   : 2
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 49
% 0.20/0.39  # Generated clauses                    : 1367
% 0.20/0.39  # ...of the previous two non-trivial   : 941
% 0.20/0.39  # Contextual simplify-reflections      : 0
% 0.20/0.39  # Paramodulations                      : 1365
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 2
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 184
% 0.20/0.39  #    Positive orientable unit clauses  : 108
% 0.20/0.39  #    Positive unorientable unit clauses: 1
% 0.20/0.39  #    Negative unit clauses             : 14
% 0.20/0.39  #    Non-unit-clauses                  : 61
% 0.20/0.39  # Current number of unprocessed clauses: 558
% 0.20/0.39  # ...number of literals in the above   : 828
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 77
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 882
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 794
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 49
% 0.20/0.39  # Unit Clause-clause subsumption calls : 275
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 263
% 0.20/0.39  # BW rewrite match successes           : 42
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 17740
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.050 s
% 0.20/0.39  # System time              : 0.004 s
% 0.20/0.39  # Total time               : 0.054 s
% 0.20/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
