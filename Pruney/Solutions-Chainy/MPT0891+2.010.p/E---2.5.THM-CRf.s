%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:54 EST 2020

% Result     : Theorem 4.47s
% Output     : CNFRefutation 4.47s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 490 expanded)
%              Number of clauses        :   58 ( 203 expanded)
%              Number of leaves         :   15 ( 121 expanded)
%              Depth                    :   14
%              Number of atoms          :  261 (1906 expanded)
%              Number of equality atoms :  193 (1526 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => ( X4 != k5_mcart_1(X1,X2,X3,X4)
                & X4 != k6_mcart_1(X1,X2,X3,X4)
                & X4 != k7_mcart_1(X1,X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).

fof(t50_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
                & k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t20_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(t48_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(t29_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k3_mcart_1(X3,X4,X5) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(t73_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_xboole_0
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0
          & ~ ! [X4] :
                ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
               => ( X4 != k5_mcart_1(X1,X2,X3,X4)
                  & X4 != k6_mcart_1(X1,X2,X3,X4)
                  & X4 != k7_mcart_1(X1,X2,X3,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t51_mcart_1])).

fof(c_0_16,plain,(
    ! [X55,X56,X57,X58] :
      ( ( k5_mcart_1(X55,X56,X57,X58) = k1_mcart_1(k1_mcart_1(X58))
        | ~ m1_subset_1(X58,k3_zfmisc_1(X55,X56,X57))
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0 )
      & ( k6_mcart_1(X55,X56,X57,X58) = k2_mcart_1(k1_mcart_1(X58))
        | ~ m1_subset_1(X58,k3_zfmisc_1(X55,X56,X57))
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0 )
      & ( k7_mcart_1(X55,X56,X57,X58) = k2_mcart_1(X58)
        | ~ m1_subset_1(X58,k3_zfmisc_1(X55,X56,X57))
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

fof(c_0_17,plain,(
    ! [X40,X41,X42] : k3_zfmisc_1(X40,X41,X42) = k2_zfmisc_1(k2_zfmisc_1(X40,X41),X42) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_18,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    & esk5_0 != k1_xboole_0
    & esk6_0 != k1_xboole_0
    & m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
    & ( esk7_0 = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
      | esk7_0 = k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
      | esk7_0 = k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_19,plain,(
    ! [X31,X32,X33] :
      ( ( r2_hidden(X31,X32)
        | ~ r2_hidden(X31,k4_xboole_0(X32,k1_tarski(X33))) )
      & ( X31 != X33
        | ~ r2_hidden(X31,k4_xboole_0(X32,k1_tarski(X33))) )
      & ( ~ r2_hidden(X31,X32)
        | X31 = X33
        | r2_hidden(X31,k4_xboole_0(X32,k1_tarski(X33))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_20,plain,(
    ! [X28] : k2_tarski(X28,X28) = k1_tarski(X28) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_21,plain,(
    ! [X29,X30] : k1_enumset1(X29,X29,X30) = k2_tarski(X29,X30) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X43,X44,X45] :
      ( ( X43 != k1_mcart_1(X43)
        | X43 != k4_tarski(X44,X45) )
      & ( X43 != k2_mcart_1(X43)
        | X43 != k4_tarski(X44,X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).

fof(c_0_23,plain,(
    ! [X51,X52,X53,X54] :
      ( X51 = k1_xboole_0
      | X52 = k1_xboole_0
      | X53 = k1_xboole_0
      | ~ m1_subset_1(X54,k3_zfmisc_1(X51,X52,X53))
      | X54 = k3_mcart_1(k5_mcart_1(X51,X52,X53,X54),k6_mcart_1(X51,X52,X53,X54),k7_mcart_1(X51,X52,X53,X54)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).

fof(c_0_24,plain,(
    ! [X37,X38,X39] : k3_mcart_1(X37,X38,X39) = k4_tarski(k4_tarski(X37,X38),X39) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_25,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( X1 != k2_mcart_1(X1)
    | X1 != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_32,plain,(
    ! [X59,X60] :
      ( k1_mcart_1(k4_tarski(X59,X60)) = X59
      & k2_mcart_1(k4_tarski(X59,X60)) = X60 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_33,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk7_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_38,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_39,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_40,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_enumset1(X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

fof(c_0_41,plain,(
    ! [X16] : k4_xboole_0(k1_xboole_0,X16) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_42,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) != k4_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_26])).

cnf(c_0_45,negated_conjecture,
    ( k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = k2_mcart_1(esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k1_enumset1(X1,X1,X1))) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_48,plain,(
    ! [X46,X48,X49,X50] :
      ( ( r2_hidden(esk3_1(X46),X46)
        | X46 = k1_xboole_0 )
      & ( ~ r2_hidden(X48,X46)
        | esk3_1(X46) != k3_mcart_1(X48,X49,X50)
        | X46 = k1_xboole_0 )
      & ( ~ r2_hidden(X49,X46)
        | esk3_1(X46) != k3_mcart_1(X48,X49,X50)
        | X46 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).

fof(c_0_49,plain,(
    ! [X17,X18,X19,X20,X21,X22,X23,X24,X25,X26] :
      ( ( ~ r2_hidden(X21,X20)
        | X21 = X17
        | X21 = X18
        | X21 = X19
        | X20 != k1_enumset1(X17,X18,X19) )
      & ( X22 != X17
        | r2_hidden(X22,X20)
        | X20 != k1_enumset1(X17,X18,X19) )
      & ( X22 != X18
        | r2_hidden(X22,X20)
        | X20 != k1_enumset1(X17,X18,X19) )
      & ( X22 != X19
        | r2_hidden(X22,X20)
        | X20 != k1_enumset1(X17,X18,X19) )
      & ( esk2_4(X23,X24,X25,X26) != X23
        | ~ r2_hidden(esk2_4(X23,X24,X25,X26),X26)
        | X26 = k1_enumset1(X23,X24,X25) )
      & ( esk2_4(X23,X24,X25,X26) != X24
        | ~ r2_hidden(esk2_4(X23,X24,X25,X26),X26)
        | X26 = k1_enumset1(X23,X24,X25) )
      & ( esk2_4(X23,X24,X25,X26) != X25
        | ~ r2_hidden(esk2_4(X23,X24,X25,X26),X26)
        | X26 = k1_enumset1(X23,X24,X25) )
      & ( r2_hidden(esk2_4(X23,X24,X25,X26),X26)
        | esk2_4(X23,X24,X25,X26) = X23
        | esk2_4(X23,X24,X25,X26) = X24
        | esk2_4(X23,X24,X25,X26) = X25
        | X26 = k1_enumset1(X23,X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_50,negated_conjecture,
    ( esk7_0 = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
    | esk7_0 = k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
    | esk7_0 = k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_51,plain,
    ( k4_tarski(X1,X2) != X2 ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( k4_tarski(k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)),k2_mcart_1(esk7_0)) = esk7_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_36]),c_0_45]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_53,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_57,negated_conjecture,
    ( k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0
    | k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0
    | k2_mcart_1(esk7_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_45])).

cnf(c_0_58,negated_conjecture,
    ( k2_mcart_1(esk7_0) != esk7_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_60,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_55])])).

cnf(c_0_62,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk3_1(X2) != k3_mcart_1(X3,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_63,negated_conjecture,
    ( k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)) = k1_mcart_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_52])).

cnf(c_0_64,negated_conjecture,
    ( k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0
    | k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0 ),
    inference(sr,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k1_enumset1(X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_66,plain,
    ( r2_hidden(esk3_1(k1_enumset1(X1,X2,X3)),k1_enumset1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

fof(c_0_67,plain,(
    ! [X34,X35,X36] :
      ( ( r2_hidden(X34,X36)
        | k4_xboole_0(k2_tarski(X34,X35),X36) != k1_xboole_0 )
      & ( r2_hidden(X35,X36)
        | k4_xboole_0(k2_tarski(X34,X35),X36) != k1_xboole_0 )
      & ( ~ r2_hidden(X34,X36)
        | ~ r2_hidden(X35,X36)
        | k4_xboole_0(k2_tarski(X34,X35),X36) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_zfmisc_1])])])).

cnf(c_0_68,plain,
    ( X2 = k1_xboole_0
    | esk3_1(X2) != k4_tarski(k4_tarski(X3,X1),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_62,c_0_34])).

cnf(c_0_69,negated_conjecture,
    ( k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),esk7_0) = k1_mcart_1(esk7_0)
    | k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,plain,
    ( esk3_1(k1_enumset1(X1,X2,X3)) = X3
    | esk3_1(k1_enumset1(X1,X2,X3)) = X2
    | esk3_1(k1_enumset1(X1,X2,X3)) = X1 ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(k2_tarski(X3,X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

fof(c_0_72,plain,(
    ! [X15] : k4_xboole_0(X15,k1_xboole_0) = X15 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_73,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk3_1(X2) != k3_mcart_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_74,negated_conjecture,
    ( k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0
    | X1 = k1_xboole_0
    | esk3_1(X1) != k4_tarski(k1_mcart_1(esk7_0),X2)
    | ~ r2_hidden(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk7_0),k2_mcart_1(esk7_0)) = esk7_0 ),
    inference(rw,[status(thm)],[c_0_52,c_0_63])).

cnf(c_0_76,plain,
    ( esk3_1(k1_enumset1(X1,X2,X2)) = X1
    | esk3_1(k1_enumset1(X1,X2,X2)) = X2 ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_70])])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(k1_enumset1(X3,X3,X1),X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_71,c_0_30])).

cnf(c_0_78,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_80,plain,
    ( X2 = k1_xboole_0
    | esk3_1(X2) != k4_tarski(k4_tarski(X1,X3),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_73,c_0_34])).

cnf(c_0_81,negated_conjecture,
    ( k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0
    | X1 = k1_xboole_0
    | esk3_1(X1) != esk7_0
    | ~ r2_hidden(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_82,plain,
    ( esk3_1(k1_enumset1(X1,X1,X1)) = X1 ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_76])])).

cnf(c_0_83,plain,
    ( k1_enumset1(X1,X1,X2) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_53])).

cnf(c_0_84,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_79])])).

cnf(c_0_85,negated_conjecture,
    ( X1 = k1_xboole_0
    | esk3_1(X1) != esk7_0
    | ~ r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_52])).

cnf(c_0_86,negated_conjecture,
    ( k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83])]),c_0_84])])).

cnf(c_0_87,negated_conjecture,
    ( X1 = k1_xboole_0
    | esk3_1(X1) != esk7_0
    | ~ r2_hidden(esk7_0,X1) ),
    inference(rw,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_88,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_82]),c_0_83])]),c_0_84])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:34:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 4.47/4.65  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 4.47/4.65  # and selection function SelectNegativeLiterals.
% 4.47/4.65  #
% 4.47/4.65  # Preprocessing time       : 0.028 s
% 4.47/4.65  # Presaturation interreduction done
% 4.47/4.65  
% 4.47/4.65  # Proof found!
% 4.47/4.65  # SZS status Theorem
% 4.47/4.65  # SZS output start CNFRefutation
% 4.47/4.65  fof(t51_mcart_1, conjecture, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_mcart_1)).
% 4.47/4.65  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 4.47/4.65  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 4.47/4.65  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 4.47/4.65  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.47/4.65  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.47/4.65  fof(t20_mcart_1, axiom, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 4.47/4.65  fof(t48_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 4.47/4.65  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 4.47/4.65  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 4.47/4.65  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 4.47/4.65  fof(t29_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k3_mcart_1(X3,X4,X5))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 4.47/4.65  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 4.47/4.65  fof(t73_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_xboole_0<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 4.47/4.65  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.47/4.65  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4))))))), inference(assume_negation,[status(cth)],[t51_mcart_1])).
% 4.47/4.65  fof(c_0_16, plain, ![X55, X56, X57, X58]:(((k5_mcart_1(X55,X56,X57,X58)=k1_mcart_1(k1_mcart_1(X58))|~m1_subset_1(X58,k3_zfmisc_1(X55,X56,X57))|(X55=k1_xboole_0|X56=k1_xboole_0|X57=k1_xboole_0))&(k6_mcart_1(X55,X56,X57,X58)=k2_mcart_1(k1_mcart_1(X58))|~m1_subset_1(X58,k3_zfmisc_1(X55,X56,X57))|(X55=k1_xboole_0|X56=k1_xboole_0|X57=k1_xboole_0)))&(k7_mcart_1(X55,X56,X57,X58)=k2_mcart_1(X58)|~m1_subset_1(X58,k3_zfmisc_1(X55,X56,X57))|(X55=k1_xboole_0|X56=k1_xboole_0|X57=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 4.47/4.65  fof(c_0_17, plain, ![X40, X41, X42]:k3_zfmisc_1(X40,X41,X42)=k2_zfmisc_1(k2_zfmisc_1(X40,X41),X42), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 4.47/4.65  fof(c_0_18, negated_conjecture, (((esk4_0!=k1_xboole_0&esk5_0!=k1_xboole_0)&esk6_0!=k1_xboole_0)&(m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))&(esk7_0=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|esk7_0=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|esk7_0=k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 4.47/4.65  fof(c_0_19, plain, ![X31, X32, X33]:(((r2_hidden(X31,X32)|~r2_hidden(X31,k4_xboole_0(X32,k1_tarski(X33))))&(X31!=X33|~r2_hidden(X31,k4_xboole_0(X32,k1_tarski(X33)))))&(~r2_hidden(X31,X32)|X31=X33|r2_hidden(X31,k4_xboole_0(X32,k1_tarski(X33))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 4.47/4.65  fof(c_0_20, plain, ![X28]:k2_tarski(X28,X28)=k1_tarski(X28), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 4.47/4.65  fof(c_0_21, plain, ![X29, X30]:k1_enumset1(X29,X29,X30)=k2_tarski(X29,X30), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 4.47/4.65  fof(c_0_22, plain, ![X43, X44, X45]:((X43!=k1_mcart_1(X43)|X43!=k4_tarski(X44,X45))&(X43!=k2_mcart_1(X43)|X43!=k4_tarski(X44,X45))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).
% 4.47/4.65  fof(c_0_23, plain, ![X51, X52, X53, X54]:(X51=k1_xboole_0|X52=k1_xboole_0|X53=k1_xboole_0|(~m1_subset_1(X54,k3_zfmisc_1(X51,X52,X53))|X54=k3_mcart_1(k5_mcart_1(X51,X52,X53,X54),k6_mcart_1(X51,X52,X53,X54),k7_mcart_1(X51,X52,X53,X54)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).
% 4.47/4.65  fof(c_0_24, plain, ![X37, X38, X39]:k3_mcart_1(X37,X38,X39)=k4_tarski(k4_tarski(X37,X38),X39), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 4.47/4.65  cnf(c_0_25, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 4.47/4.65  cnf(c_0_26, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 4.47/4.65  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 4.47/4.65  cnf(c_0_28, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 4.47/4.65  cnf(c_0_29, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 4.47/4.65  cnf(c_0_30, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.47/4.65  cnf(c_0_31, plain, (X1!=k2_mcart_1(X1)|X1!=k4_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 4.47/4.65  fof(c_0_32, plain, ![X59, X60]:(k1_mcart_1(k4_tarski(X59,X60))=X59&k2_mcart_1(k4_tarski(X59,X60))=X60), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 4.47/4.65  cnf(c_0_33, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 4.47/4.65  cnf(c_0_34, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 4.47/4.65  cnf(c_0_35, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 4.47/4.65  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk7_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[c_0_27, c_0_26])).
% 4.47/4.65  cnf(c_0_37, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 4.47/4.65  cnf(c_0_38, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 4.47/4.65  cnf(c_0_39, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 4.47/4.65  cnf(c_0_40, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_enumset1(X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 4.47/4.65  fof(c_0_41, plain, ![X16]:k4_xboole_0(k1_xboole_0,X16)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 4.47/4.65  cnf(c_0_42, plain, (k2_mcart_1(k4_tarski(X1,X2))!=k4_tarski(X1,X2)), inference(er,[status(thm)],[c_0_31])).
% 4.47/4.65  cnf(c_0_43, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_32])).
% 4.47/4.65  cnf(c_0_44, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X4=k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_26])).
% 4.47/4.65  cnf(c_0_45, negated_conjecture, (k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=k2_mcart_1(esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 4.47/4.65  cnf(c_0_46, plain, (~r2_hidden(X1,k4_xboole_0(X2,k1_enumset1(X1,X1,X1)))), inference(er,[status(thm)],[c_0_40])).
% 4.47/4.65  cnf(c_0_47, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 4.47/4.65  fof(c_0_48, plain, ![X46, X48, X49, X50]:((r2_hidden(esk3_1(X46),X46)|X46=k1_xboole_0)&((~r2_hidden(X48,X46)|esk3_1(X46)!=k3_mcart_1(X48,X49,X50)|X46=k1_xboole_0)&(~r2_hidden(X49,X46)|esk3_1(X46)!=k3_mcart_1(X48,X49,X50)|X46=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).
% 4.47/4.65  fof(c_0_49, plain, ![X17, X18, X19, X20, X21, X22, X23, X24, X25, X26]:(((~r2_hidden(X21,X20)|(X21=X17|X21=X18|X21=X19)|X20!=k1_enumset1(X17,X18,X19))&(((X22!=X17|r2_hidden(X22,X20)|X20!=k1_enumset1(X17,X18,X19))&(X22!=X18|r2_hidden(X22,X20)|X20!=k1_enumset1(X17,X18,X19)))&(X22!=X19|r2_hidden(X22,X20)|X20!=k1_enumset1(X17,X18,X19))))&((((esk2_4(X23,X24,X25,X26)!=X23|~r2_hidden(esk2_4(X23,X24,X25,X26),X26)|X26=k1_enumset1(X23,X24,X25))&(esk2_4(X23,X24,X25,X26)!=X24|~r2_hidden(esk2_4(X23,X24,X25,X26),X26)|X26=k1_enumset1(X23,X24,X25)))&(esk2_4(X23,X24,X25,X26)!=X25|~r2_hidden(esk2_4(X23,X24,X25,X26),X26)|X26=k1_enumset1(X23,X24,X25)))&(r2_hidden(esk2_4(X23,X24,X25,X26),X26)|(esk2_4(X23,X24,X25,X26)=X23|esk2_4(X23,X24,X25,X26)=X24|esk2_4(X23,X24,X25,X26)=X25)|X26=k1_enumset1(X23,X24,X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 4.47/4.65  cnf(c_0_50, negated_conjecture, (esk7_0=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|esk7_0=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|esk7_0=k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 4.47/4.65  cnf(c_0_51, plain, (k4_tarski(X1,X2)!=X2), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 4.47/4.65  cnf(c_0_52, negated_conjecture, (k4_tarski(k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)),k2_mcart_1(esk7_0))=esk7_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_36]), c_0_45]), c_0_37]), c_0_38]), c_0_39])).
% 4.47/4.65  cnf(c_0_53, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 4.47/4.65  cnf(c_0_54, plain, (r2_hidden(esk3_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_48])).
% 4.47/4.65  cnf(c_0_55, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 4.47/4.65  cnf(c_0_56, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 4.47/4.65  cnf(c_0_57, negated_conjecture, (k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0|k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0|k2_mcart_1(esk7_0)=esk7_0), inference(spm,[status(thm)],[c_0_50, c_0_45])).
% 4.47/4.65  cnf(c_0_58, negated_conjecture, (k2_mcart_1(esk7_0)!=esk7_0), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 4.47/4.65  cnf(c_0_59, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 4.47/4.65  cnf(c_0_60, plain, (r2_hidden(esk3_1(X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 4.47/4.65  cnf(c_0_61, plain, (r2_hidden(X1,k1_enumset1(X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_55])])).
% 4.47/4.65  cnf(c_0_62, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk3_1(X2)!=k3_mcart_1(X3,X1,X4)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 4.47/4.65  cnf(c_0_63, negated_conjecture, (k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0))=k1_mcart_1(esk7_0)), inference(spm,[status(thm)],[c_0_56, c_0_52])).
% 4.47/4.65  cnf(c_0_64, negated_conjecture, (k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0|k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0), inference(sr,[status(thm)],[c_0_57, c_0_58])).
% 4.47/4.65  cnf(c_0_65, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k1_enumset1(X4,X3,X2))), inference(er,[status(thm)],[c_0_59])).
% 4.47/4.65  cnf(c_0_66, plain, (r2_hidden(esk3_1(k1_enumset1(X1,X2,X3)),k1_enumset1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 4.47/4.65  fof(c_0_67, plain, ![X34, X35, X36]:(((r2_hidden(X34,X36)|k4_xboole_0(k2_tarski(X34,X35),X36)!=k1_xboole_0)&(r2_hidden(X35,X36)|k4_xboole_0(k2_tarski(X34,X35),X36)!=k1_xboole_0))&(~r2_hidden(X34,X36)|~r2_hidden(X35,X36)|k4_xboole_0(k2_tarski(X34,X35),X36)=k1_xboole_0)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_zfmisc_1])])])).
% 4.47/4.65  cnf(c_0_68, plain, (X2=k1_xboole_0|esk3_1(X2)!=k4_tarski(k4_tarski(X3,X1),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_62, c_0_34])).
% 4.47/4.65  cnf(c_0_69, negated_conjecture, (k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),esk7_0)=k1_mcart_1(esk7_0)|k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 4.47/4.65  cnf(c_0_70, plain, (esk3_1(k1_enumset1(X1,X2,X3))=X3|esk3_1(k1_enumset1(X1,X2,X3))=X2|esk3_1(k1_enumset1(X1,X2,X3))=X1), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 4.47/4.65  cnf(c_0_71, plain, (r2_hidden(X1,X2)|k4_xboole_0(k2_tarski(X3,X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_67])).
% 4.47/4.65  fof(c_0_72, plain, ![X15]:k4_xboole_0(X15,k1_xboole_0)=X15, inference(variable_rename,[status(thm)],[t3_boole])).
% 4.47/4.65  cnf(c_0_73, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk3_1(X2)!=k3_mcart_1(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 4.47/4.65  cnf(c_0_74, negated_conjecture, (k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0|X1=k1_xboole_0|esk3_1(X1)!=k4_tarski(k1_mcart_1(esk7_0),X2)|~r2_hidden(esk7_0,X1)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 4.47/4.65  cnf(c_0_75, negated_conjecture, (k4_tarski(k1_mcart_1(esk7_0),k2_mcart_1(esk7_0))=esk7_0), inference(rw,[status(thm)],[c_0_52, c_0_63])).
% 4.47/4.65  cnf(c_0_76, plain, (esk3_1(k1_enumset1(X1,X2,X2))=X1|esk3_1(k1_enumset1(X1,X2,X2))=X2), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_70])])).
% 4.47/4.65  cnf(c_0_77, plain, (r2_hidden(X1,X2)|k4_xboole_0(k1_enumset1(X3,X3,X1),X2)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_71, c_0_30])).
% 4.47/4.65  cnf(c_0_78, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_72])).
% 4.47/4.65  cnf(c_0_79, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 4.47/4.65  cnf(c_0_80, plain, (X2=k1_xboole_0|esk3_1(X2)!=k4_tarski(k4_tarski(X1,X3),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_73, c_0_34])).
% 4.47/4.65  cnf(c_0_81, negated_conjecture, (k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0|X1=k1_xboole_0|esk3_1(X1)!=esk7_0|~r2_hidden(esk7_0,X1)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 4.47/4.65  cnf(c_0_82, plain, (esk3_1(k1_enumset1(X1,X1,X1))=X1), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_76])])).
% 4.47/4.65  cnf(c_0_83, plain, (k1_enumset1(X1,X1,X2)!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_53])).
% 4.47/4.65  cnf(c_0_84, plain, (r2_hidden(X1,k1_enumset1(X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_79])])).
% 4.47/4.65  cnf(c_0_85, negated_conjecture, (X1=k1_xboole_0|esk3_1(X1)!=esk7_0|~r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),X1)), inference(spm,[status(thm)],[c_0_80, c_0_52])).
% 4.47/4.65  cnf(c_0_86, negated_conjecture, (k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_83])]), c_0_84])])).
% 4.47/4.65  cnf(c_0_87, negated_conjecture, (X1=k1_xboole_0|esk3_1(X1)!=esk7_0|~r2_hidden(esk7_0,X1)), inference(rw,[status(thm)],[c_0_85, c_0_86])).
% 4.47/4.65  cnf(c_0_88, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_82]), c_0_83])]), c_0_84])]), ['proof']).
% 4.47/4.65  # SZS output end CNFRefutation
% 4.47/4.65  # Proof object total steps             : 89
% 4.47/4.65  # Proof object clause steps            : 58
% 4.47/4.65  # Proof object formula steps           : 31
% 4.47/4.65  # Proof object conjectures             : 23
% 4.47/4.65  # Proof object clause conjectures      : 20
% 4.47/4.65  # Proof object formula conjectures     : 3
% 4.47/4.65  # Proof object initial clauses used    : 24
% 4.47/4.65  # Proof object initial formulas used   : 15
% 4.47/4.65  # Proof object generating inferences   : 18
% 4.47/4.65  # Proof object simplifying inferences  : 38
% 4.47/4.65  # Training examples: 0 positive, 0 negative
% 4.47/4.65  # Parsed axioms                        : 16
% 4.47/4.65  # Removed by relevancy pruning/SinE    : 0
% 4.47/4.65  # Initial clauses                      : 42
% 4.47/4.65  # Removed in clause preprocessing      : 4
% 4.47/4.65  # Initial clauses in saturation        : 38
% 4.47/4.65  # Processed clauses                    : 12133
% 4.47/4.65  # ...of these trivial                  : 316
% 4.47/4.65  # ...subsumed                          : 9926
% 4.47/4.65  # ...remaining for further processing  : 1891
% 4.47/4.65  # Other redundant clauses eliminated   : 35085
% 4.47/4.65  # Clauses deleted for lack of memory   : 0
% 4.47/4.65  # Backward-subsumed                    : 81
% 4.47/4.65  # Backward-rewritten                   : 168
% 4.47/4.65  # Generated clauses                    : 571625
% 4.47/4.65  # ...of the previous two non-trivial   : 477915
% 4.47/4.65  # Contextual simplify-reflections      : 18
% 4.47/4.65  # Paramodulations                      : 536382
% 4.47/4.65  # Factorizations                       : 157
% 4.47/4.65  # Equation resolutions                 : 35088
% 4.47/4.65  # Propositional unsat checks           : 0
% 4.47/4.65  #    Propositional check models        : 0
% 4.47/4.65  #    Propositional check unsatisfiable : 0
% 4.47/4.65  #    Propositional clauses             : 0
% 4.47/4.65  #    Propositional clauses after purity: 0
% 4.47/4.65  #    Propositional unsat core size     : 0
% 4.47/4.65  #    Propositional preprocessing time  : 0.000
% 4.47/4.65  #    Propositional encoding time       : 0.000
% 4.47/4.65  #    Propositional solver time         : 0.000
% 4.47/4.65  #    Success case prop preproc time    : 0.000
% 4.47/4.65  #    Success case prop encoding time   : 0.000
% 4.47/4.65  #    Success case prop solver time     : 0.000
% 4.47/4.65  # Current number of processed clauses  : 1594
% 4.47/4.65  #    Positive orientable unit clauses  : 96
% 4.47/4.65  #    Positive unorientable unit clauses: 0
% 4.47/4.65  #    Negative unit clauses             : 21
% 4.47/4.65  #    Non-unit-clauses                  : 1477
% 4.47/4.65  # Current number of unprocessed clauses: 465304
% 4.47/4.65  # ...number of literals in the above   : 2180967
% 4.47/4.65  # Current number of archived formulas  : 0
% 4.47/4.65  # Current number of archived clauses   : 291
% 4.47/4.65  # Clause-clause subsumption calls (NU) : 236069
% 4.47/4.65  # Rec. Clause-clause subsumption calls : 134058
% 4.47/4.65  # Non-unit clause-clause subsumptions  : 8104
% 4.47/4.65  # Unit Clause-clause subsumption calls : 8881
% 4.47/4.65  # Rewrite failures with RHS unbound    : 0
% 4.47/4.65  # BW rewrite match attempts            : 822
% 4.47/4.65  # BW rewrite match successes           : 24
% 4.47/4.65  # Condensation attempts                : 0
% 4.47/4.65  # Condensation successes               : 0
% 4.47/4.65  # Termbank termtop insertions          : 11381600
% 4.51/4.67  
% 4.51/4.67  # -------------------------------------------------
% 4.51/4.67  # User time                : 4.111 s
% 4.51/4.67  # System time              : 0.211 s
% 4.51/4.67  # Total time               : 4.322 s
% 4.51/4.67  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
