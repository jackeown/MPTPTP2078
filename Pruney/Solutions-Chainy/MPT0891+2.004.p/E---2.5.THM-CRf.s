%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:53 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 (1201 expanded)
%              Number of clauses        :   53 ( 497 expanded)
%              Number of leaves         :   13 ( 294 expanded)
%              Depth                    :   14
%              Number of atoms          :  271 (5189 expanded)
%              Number of equality atoms :  180 (4068 expanded)
%              Maximal formula depth    :   22 (   5 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t48_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(t20_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(t29_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k3_mcart_1(X3,X4,X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(c_0_13,negated_conjecture,(
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

fof(c_0_14,plain,(
    ! [X57,X58,X59,X60] :
      ( ( k5_mcart_1(X57,X58,X59,X60) = k1_mcart_1(k1_mcart_1(X60))
        | ~ m1_subset_1(X60,k3_zfmisc_1(X57,X58,X59))
        | X57 = k1_xboole_0
        | X58 = k1_xboole_0
        | X59 = k1_xboole_0 )
      & ( k6_mcart_1(X57,X58,X59,X60) = k2_mcart_1(k1_mcart_1(X60))
        | ~ m1_subset_1(X60,k3_zfmisc_1(X57,X58,X59))
        | X57 = k1_xboole_0
        | X58 = k1_xboole_0
        | X59 = k1_xboole_0 )
      & ( k7_mcart_1(X57,X58,X59,X60) = k2_mcart_1(X60)
        | ~ m1_subset_1(X60,k3_zfmisc_1(X57,X58,X59))
        | X57 = k1_xboole_0
        | X58 = k1_xboole_0
        | X59 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

fof(c_0_15,plain,(
    ! [X42,X43,X44] : k3_zfmisc_1(X42,X43,X44) = k2_zfmisc_1(k2_zfmisc_1(X42,X43),X44) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_16,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    & esk6_0 != k1_xboole_0
    & esk7_0 != k1_xboole_0
    & m1_subset_1(esk8_0,k3_zfmisc_1(esk5_0,esk6_0,esk7_0))
    & ( esk8_0 = k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)
      | esk8_0 = k6_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)
      | esk8_0 = k7_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_17,plain,(
    ! [X53,X54,X55,X56] :
      ( X53 = k1_xboole_0
      | X54 = k1_xboole_0
      | X55 = k1_xboole_0
      | ~ m1_subset_1(X56,k3_zfmisc_1(X53,X54,X55))
      | X56 = k3_mcart_1(k5_mcart_1(X53,X54,X55,X56),k6_mcart_1(X53,X54,X55,X56),k7_mcart_1(X53,X54,X55,X56)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).

fof(c_0_18,plain,(
    ! [X39,X40,X41] : k3_mcart_1(X39,X40,X41) = k4_tarski(k4_tarski(X39,X40),X41) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_19,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk8_0,k3_zfmisc_1(esk5_0,esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X26,X27,X28,X29,X30,X31] :
      ( ( ~ r2_hidden(X28,X27)
        | X28 = X26
        | X27 != k1_tarski(X26) )
      & ( X29 != X26
        | r2_hidden(X29,X27)
        | X27 != k1_tarski(X26) )
      & ( ~ r2_hidden(esk3_2(X30,X31),X31)
        | esk3_2(X30,X31) != X30
        | X31 = k1_tarski(X30) )
      & ( r2_hidden(esk3_2(X30,X31),X31)
        | esk3_2(X30,X31) = X30
        | X31 = k1_tarski(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_23,plain,(
    ! [X33] : k2_tarski(X33,X33) = k1_tarski(X33) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_24,plain,(
    ! [X34,X35] : k1_enumset1(X34,X34,X35) = k2_tarski(X34,X35) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_25,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22,X23,X24] :
      ( ( ~ r2_hidden(X19,X18)
        | X19 = X15
        | X19 = X16
        | X19 = X17
        | X18 != k1_enumset1(X15,X16,X17) )
      & ( X20 != X15
        | r2_hidden(X20,X18)
        | X18 != k1_enumset1(X15,X16,X17) )
      & ( X20 != X16
        | r2_hidden(X20,X18)
        | X18 != k1_enumset1(X15,X16,X17) )
      & ( X20 != X17
        | r2_hidden(X20,X18)
        | X18 != k1_enumset1(X15,X16,X17) )
      & ( esk2_4(X21,X22,X23,X24) != X21
        | ~ r2_hidden(esk2_4(X21,X22,X23,X24),X24)
        | X24 = k1_enumset1(X21,X22,X23) )
      & ( esk2_4(X21,X22,X23,X24) != X22
        | ~ r2_hidden(esk2_4(X21,X22,X23,X24),X24)
        | X24 = k1_enumset1(X21,X22,X23) )
      & ( esk2_4(X21,X22,X23,X24) != X23
        | ~ r2_hidden(esk2_4(X21,X22,X23,X24),X24)
        | X24 = k1_enumset1(X21,X22,X23) )
      & ( r2_hidden(esk2_4(X21,X22,X23,X24),X24)
        | esk2_4(X21,X22,X23,X24) = X21
        | esk2_4(X21,X22,X23,X24) = X22
        | esk2_4(X21,X22,X23,X24) = X23
        | X24 = k1_enumset1(X21,X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_26,plain,(
    ! [X45,X46,X47] :
      ( ( X45 != k1_mcart_1(X45)
        | X45 != k4_tarski(X46,X47) )
      & ( X45 != k2_mcart_1(X45)
        | X45 != k4_tarski(X46,X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).

fof(c_0_27,plain,(
    ! [X48,X50,X51,X52] :
      ( ( r2_hidden(esk4_1(X48),X48)
        | X48 = k1_xboole_0 )
      & ( ~ r2_hidden(X50,X48)
        | esk4_1(X48) != k3_mcart_1(X50,X51,X52)
        | X48 = k1_xboole_0 )
      & ( ~ r2_hidden(X51,X48)
        | esk4_1(X48) != k3_mcart_1(X50,X51,X52)
        | X48 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_35,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,plain,
    ( X1 != k2_mcart_1(X1)
    | X1 != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_40,plain,(
    ! [X61,X62] :
      ( k1_mcart_1(k4_tarski(X61,X62)) = X61
      & k2_mcart_1(k4_tarski(X61,X62)) = X62 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_41,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk4_1(X2) != k3_mcart_1(X3,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_20])).

cnf(c_0_43,negated_conjecture,
    ( k7_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0) = k2_mcart_1(esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_44,plain,
    ( X1 = X3
    | X2 != k1_enumset1(X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_38])])).

cnf(c_0_46,plain,
    ( r2_hidden(esk4_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_47,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) != k4_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk4_1(X2) != k3_mcart_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_50,plain,
    ( X2 = k1_xboole_0
    | esk4_1(X2) != k4_tarski(k4_tarski(X3,X1),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_41,c_0_29])).

cnf(c_0_51,negated_conjecture,
    ( k4_tarski(k4_tarski(k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0),k6_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)),k2_mcart_1(esk8_0)) = esk8_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_31]),c_0_43]),c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_52,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_enumset1(X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_53,plain,
    ( r2_hidden(esk4_1(k1_enumset1(X1,X2,X3)),k1_enumset1(X1,X2,X3))
    | r2_hidden(X3,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( esk8_0 = k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)
    | esk8_0 = k6_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)
    | esk8_0 = k7_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_55,plain,
    ( k4_tarski(X1,X2) != X2 ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,plain,
    ( X2 = k1_xboole_0
    | esk4_1(X2) != k4_tarski(k4_tarski(X1,X3),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_49,c_0_29])).

cnf(c_0_57,negated_conjecture,
    ( X1 = k1_xboole_0
    | esk4_1(X1) != esk8_0
    | ~ r2_hidden(k6_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0),X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,plain,
    ( esk4_1(k1_enumset1(X1,X1,X1)) = X1
    | r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( k6_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0) = esk8_0
    | k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0) = esk8_0
    | k2_mcart_1(esk8_0) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_43])).

cnf(c_0_60,negated_conjecture,
    ( k2_mcart_1(esk8_0) != esk8_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_51])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_62,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( r2_hidden(X9,X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X6)
        | r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X12)
        | X13 = k4_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X12)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k4_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_63,negated_conjecture,
    ( X1 = k1_xboole_0
    | esk4_1(X1) != esk8_0
    | ~ r2_hidden(k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0),X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_51])).

cnf(c_0_64,negated_conjecture,
    ( k1_enumset1(esk8_0,esk8_0,esk8_0) = k1_xboole_0
    | r2_hidden(esk8_0,k1_xboole_0)
    | ~ r2_hidden(k6_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0),k1_enumset1(esk8_0,esk8_0,esk8_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58])])).

cnf(c_0_65,negated_conjecture,
    ( k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0) = esk8_0
    | k6_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0) = esk8_0 ),
    inference(sr,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_61])])).

cnf(c_0_67,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( k1_enumset1(esk8_0,esk8_0,esk8_0) = k1_xboole_0
    | r2_hidden(esk8_0,k1_xboole_0)
    | ~ r2_hidden(k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0),k1_enumset1(esk8_0,esk8_0,esk8_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_58])])).

cnf(c_0_69,negated_conjecture,
    ( k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0) = esk8_0
    | k1_enumset1(esk8_0,esk8_0,esk8_0) = k1_xboole_0
    | r2_hidden(esk8_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])])).

cnf(c_0_70,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( k1_enumset1(esk8_0,esk8_0,esk8_0) = k1_xboole_0
    | r2_hidden(esk8_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_66])])).

cnf(c_0_72,plain,
    ( r2_hidden(esk4_1(k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))
    | ~ r2_hidden(X3,k1_xboole_0)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_46])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk8_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_71])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk4_1(k4_xboole_0(X1,k1_xboole_0)),k4_xboole_0(X1,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_73])])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( ~ r2_hidden(esk4_1(k4_xboole_0(X1,k1_xboole_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk4_1(k4_xboole_0(X1,k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_77,c_0_78]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:26:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.47  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.21/0.47  # and selection function SelectNegativeLiterals.
% 0.21/0.47  #
% 0.21/0.47  # Preprocessing time       : 0.044 s
% 0.21/0.47  # Presaturation interreduction done
% 0.21/0.47  
% 0.21/0.47  # Proof found!
% 0.21/0.47  # SZS status Theorem
% 0.21/0.47  # SZS output start CNFRefutation
% 0.21/0.47  fof(t51_mcart_1, conjecture, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_mcart_1)).
% 0.21/0.47  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.21/0.47  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.21/0.47  fof(t48_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 0.21/0.47  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.21/0.47  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.21/0.47  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.47  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.47  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.21/0.47  fof(t20_mcart_1, axiom, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.21/0.47  fof(t29_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k3_mcart_1(X3,X4,X5))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 0.21/0.47  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.21/0.47  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.21/0.47  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4))))))), inference(assume_negation,[status(cth)],[t51_mcart_1])).
% 0.21/0.47  fof(c_0_14, plain, ![X57, X58, X59, X60]:(((k5_mcart_1(X57,X58,X59,X60)=k1_mcart_1(k1_mcart_1(X60))|~m1_subset_1(X60,k3_zfmisc_1(X57,X58,X59))|(X57=k1_xboole_0|X58=k1_xboole_0|X59=k1_xboole_0))&(k6_mcart_1(X57,X58,X59,X60)=k2_mcart_1(k1_mcart_1(X60))|~m1_subset_1(X60,k3_zfmisc_1(X57,X58,X59))|(X57=k1_xboole_0|X58=k1_xboole_0|X59=k1_xboole_0)))&(k7_mcart_1(X57,X58,X59,X60)=k2_mcart_1(X60)|~m1_subset_1(X60,k3_zfmisc_1(X57,X58,X59))|(X57=k1_xboole_0|X58=k1_xboole_0|X59=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.21/0.47  fof(c_0_15, plain, ![X42, X43, X44]:k3_zfmisc_1(X42,X43,X44)=k2_zfmisc_1(k2_zfmisc_1(X42,X43),X44), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.21/0.47  fof(c_0_16, negated_conjecture, (((esk5_0!=k1_xboole_0&esk6_0!=k1_xboole_0)&esk7_0!=k1_xboole_0)&(m1_subset_1(esk8_0,k3_zfmisc_1(esk5_0,esk6_0,esk7_0))&(esk8_0=k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)|esk8_0=k6_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)|esk8_0=k7_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.21/0.47  fof(c_0_17, plain, ![X53, X54, X55, X56]:(X53=k1_xboole_0|X54=k1_xboole_0|X55=k1_xboole_0|(~m1_subset_1(X56,k3_zfmisc_1(X53,X54,X55))|X56=k3_mcart_1(k5_mcart_1(X53,X54,X55,X56),k6_mcart_1(X53,X54,X55,X56),k7_mcart_1(X53,X54,X55,X56)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).
% 0.21/0.47  fof(c_0_18, plain, ![X39, X40, X41]:k3_mcart_1(X39,X40,X41)=k4_tarski(k4_tarski(X39,X40),X41), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.21/0.47  cnf(c_0_19, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.47  cnf(c_0_20, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.47  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk8_0,k3_zfmisc_1(esk5_0,esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.47  fof(c_0_22, plain, ![X26, X27, X28, X29, X30, X31]:(((~r2_hidden(X28,X27)|X28=X26|X27!=k1_tarski(X26))&(X29!=X26|r2_hidden(X29,X27)|X27!=k1_tarski(X26)))&((~r2_hidden(esk3_2(X30,X31),X31)|esk3_2(X30,X31)!=X30|X31=k1_tarski(X30))&(r2_hidden(esk3_2(X30,X31),X31)|esk3_2(X30,X31)=X30|X31=k1_tarski(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.21/0.47  fof(c_0_23, plain, ![X33]:k2_tarski(X33,X33)=k1_tarski(X33), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.47  fof(c_0_24, plain, ![X34, X35]:k1_enumset1(X34,X34,X35)=k2_tarski(X34,X35), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.47  fof(c_0_25, plain, ![X15, X16, X17, X18, X19, X20, X21, X22, X23, X24]:(((~r2_hidden(X19,X18)|(X19=X15|X19=X16|X19=X17)|X18!=k1_enumset1(X15,X16,X17))&(((X20!=X15|r2_hidden(X20,X18)|X18!=k1_enumset1(X15,X16,X17))&(X20!=X16|r2_hidden(X20,X18)|X18!=k1_enumset1(X15,X16,X17)))&(X20!=X17|r2_hidden(X20,X18)|X18!=k1_enumset1(X15,X16,X17))))&((((esk2_4(X21,X22,X23,X24)!=X21|~r2_hidden(esk2_4(X21,X22,X23,X24),X24)|X24=k1_enumset1(X21,X22,X23))&(esk2_4(X21,X22,X23,X24)!=X22|~r2_hidden(esk2_4(X21,X22,X23,X24),X24)|X24=k1_enumset1(X21,X22,X23)))&(esk2_4(X21,X22,X23,X24)!=X23|~r2_hidden(esk2_4(X21,X22,X23,X24),X24)|X24=k1_enumset1(X21,X22,X23)))&(r2_hidden(esk2_4(X21,X22,X23,X24),X24)|(esk2_4(X21,X22,X23,X24)=X21|esk2_4(X21,X22,X23,X24)=X22|esk2_4(X21,X22,X23,X24)=X23)|X24=k1_enumset1(X21,X22,X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.21/0.47  fof(c_0_26, plain, ![X45, X46, X47]:((X45!=k1_mcart_1(X45)|X45!=k4_tarski(X46,X47))&(X45!=k2_mcart_1(X45)|X45!=k4_tarski(X46,X47))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).
% 0.21/0.47  fof(c_0_27, plain, ![X48, X50, X51, X52]:((r2_hidden(esk4_1(X48),X48)|X48=k1_xboole_0)&((~r2_hidden(X50,X48)|esk4_1(X48)!=k3_mcart_1(X50,X51,X52)|X48=k1_xboole_0)&(~r2_hidden(X51,X48)|esk4_1(X48)!=k3_mcart_1(X50,X51,X52)|X48=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).
% 0.21/0.47  cnf(c_0_28, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.47  cnf(c_0_29, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.47  cnf(c_0_30, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.21/0.47  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0))), inference(rw,[status(thm)],[c_0_21, c_0_20])).
% 0.21/0.47  cnf(c_0_32, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.47  cnf(c_0_33, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.47  cnf(c_0_34, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.47  cnf(c_0_35, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.47  cnf(c_0_36, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.47  cnf(c_0_37, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.47  cnf(c_0_38, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.47  cnf(c_0_39, plain, (X1!=k2_mcart_1(X1)|X1!=k4_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.47  fof(c_0_40, plain, ![X61, X62]:(k1_mcart_1(k4_tarski(X61,X62))=X61&k2_mcart_1(k4_tarski(X61,X62))=X62), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.21/0.47  cnf(c_0_41, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk4_1(X2)!=k3_mcart_1(X3,X1,X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.47  cnf(c_0_42, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X4=k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_20])).
% 0.21/0.47  cnf(c_0_43, negated_conjecture, (k7_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)=k2_mcart_1(esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33]), c_0_34])).
% 0.21/0.47  cnf(c_0_44, plain, (X1=X3|X2!=k1_enumset1(X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.21/0.47  cnf(c_0_45, plain, (r2_hidden(X1,k1_enumset1(X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_38])])).
% 0.21/0.47  cnf(c_0_46, plain, (r2_hidden(esk4_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.47  cnf(c_0_47, plain, (k2_mcart_1(k4_tarski(X1,X2))!=k4_tarski(X1,X2)), inference(er,[status(thm)],[c_0_39])).
% 0.21/0.47  cnf(c_0_48, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.47  cnf(c_0_49, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk4_1(X2)!=k3_mcart_1(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.47  cnf(c_0_50, plain, (X2=k1_xboole_0|esk4_1(X2)!=k4_tarski(k4_tarski(X3,X1),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_41, c_0_29])).
% 0.21/0.47  cnf(c_0_51, negated_conjecture, (k4_tarski(k4_tarski(k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0),k6_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)),k2_mcart_1(esk8_0))=esk8_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_31]), c_0_43]), c_0_32]), c_0_33]), c_0_34])).
% 0.21/0.47  cnf(c_0_52, plain, (X1=X2|~r2_hidden(X1,k1_enumset1(X2,X2,X2))), inference(er,[status(thm)],[c_0_44])).
% 0.21/0.47  cnf(c_0_53, plain, (r2_hidden(esk4_1(k1_enumset1(X1,X2,X3)),k1_enumset1(X1,X2,X3))|r2_hidden(X3,k1_xboole_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.21/0.47  cnf(c_0_54, negated_conjecture, (esk8_0=k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)|esk8_0=k6_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)|esk8_0=k7_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.47  cnf(c_0_55, plain, (k4_tarski(X1,X2)!=X2), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 0.21/0.47  cnf(c_0_56, plain, (X2=k1_xboole_0|esk4_1(X2)!=k4_tarski(k4_tarski(X1,X3),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_49, c_0_29])).
% 0.21/0.47  cnf(c_0_57, negated_conjecture, (X1=k1_xboole_0|esk4_1(X1)!=esk8_0|~r2_hidden(k6_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0),X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.21/0.47  cnf(c_0_58, plain, (esk4_1(k1_enumset1(X1,X1,X1))=X1|r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.21/0.47  cnf(c_0_59, negated_conjecture, (k6_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)=esk8_0|k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)=esk8_0|k2_mcart_1(esk8_0)=esk8_0), inference(spm,[status(thm)],[c_0_54, c_0_43])).
% 0.21/0.47  cnf(c_0_60, negated_conjecture, (k2_mcart_1(esk8_0)!=esk8_0), inference(spm,[status(thm)],[c_0_55, c_0_51])).
% 0.21/0.47  cnf(c_0_61, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.47  fof(c_0_62, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7))&(~r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k4_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k4_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))&(~r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.21/0.47  cnf(c_0_63, negated_conjecture, (X1=k1_xboole_0|esk4_1(X1)!=esk8_0|~r2_hidden(k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0),X1)), inference(spm,[status(thm)],[c_0_56, c_0_51])).
% 0.21/0.47  cnf(c_0_64, negated_conjecture, (k1_enumset1(esk8_0,esk8_0,esk8_0)=k1_xboole_0|r2_hidden(esk8_0,k1_xboole_0)|~r2_hidden(k6_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0),k1_enumset1(esk8_0,esk8_0,esk8_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58])])).
% 0.21/0.47  cnf(c_0_65, negated_conjecture, (k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)=esk8_0|k6_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)=esk8_0), inference(sr,[status(thm)],[c_0_59, c_0_60])).
% 0.21/0.47  cnf(c_0_66, plain, (r2_hidden(X1,k1_enumset1(X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_61])])).
% 0.21/0.47  cnf(c_0_67, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.21/0.47  cnf(c_0_68, negated_conjecture, (k1_enumset1(esk8_0,esk8_0,esk8_0)=k1_xboole_0|r2_hidden(esk8_0,k1_xboole_0)|~r2_hidden(k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0),k1_enumset1(esk8_0,esk8_0,esk8_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_58])])).
% 0.21/0.47  cnf(c_0_69, negated_conjecture, (k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)=esk8_0|k1_enumset1(esk8_0,esk8_0,esk8_0)=k1_xboole_0|r2_hidden(esk8_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])])).
% 0.21/0.47  cnf(c_0_70, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_67])).
% 0.21/0.47  cnf(c_0_71, negated_conjecture, (k1_enumset1(esk8_0,esk8_0,esk8_0)=k1_xboole_0|r2_hidden(esk8_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_66])])).
% 0.21/0.47  cnf(c_0_72, plain, (r2_hidden(esk4_1(k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))|~r2_hidden(X3,k1_xboole_0)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_70, c_0_46])).
% 0.21/0.47  cnf(c_0_73, negated_conjecture, (r2_hidden(esk8_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_66, c_0_71])).
% 0.21/0.47  cnf(c_0_74, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.21/0.47  cnf(c_0_75, negated_conjecture, (r2_hidden(esk4_1(k4_xboole_0(X1,k1_xboole_0)),k4_xboole_0(X1,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_73])])).
% 0.21/0.47  cnf(c_0_76, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_74])).
% 0.21/0.47  cnf(c_0_77, negated_conjecture, (~r2_hidden(esk4_1(k4_xboole_0(X1,k1_xboole_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_70, c_0_75])).
% 0.21/0.47  cnf(c_0_78, negated_conjecture, (r2_hidden(esk4_1(k4_xboole_0(X1,k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_76, c_0_75])).
% 0.21/0.47  cnf(c_0_79, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_77, c_0_78]), ['proof']).
% 0.21/0.47  # SZS output end CNFRefutation
% 0.21/0.47  # Proof object total steps             : 80
% 0.21/0.47  # Proof object clause steps            : 53
% 0.21/0.47  # Proof object formula steps           : 27
% 0.21/0.47  # Proof object conjectures             : 25
% 0.21/0.47  # Proof object clause conjectures      : 22
% 0.21/0.47  # Proof object formula conjectures     : 3
% 0.21/0.47  # Proof object initial clauses used    : 21
% 0.21/0.47  # Proof object initial formulas used   : 13
% 0.21/0.47  # Proof object generating inferences   : 18
% 0.21/0.47  # Proof object simplifying inferences  : 33
% 0.21/0.47  # Training examples: 0 positive, 0 negative
% 0.21/0.47  # Parsed axioms                        : 14
% 0.21/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.47  # Initial clauses                      : 41
% 0.21/0.47  # Removed in clause preprocessing      : 4
% 0.21/0.47  # Initial clauses in saturation        : 37
% 0.21/0.47  # Processed clauses                    : 392
% 0.21/0.47  # ...of these trivial                  : 5
% 0.21/0.47  # ...subsumed                          : 143
% 0.21/0.47  # ...remaining for further processing  : 244
% 0.21/0.47  # Other redundant clauses eliminated   : 248
% 0.21/0.47  # Clauses deleted for lack of memory   : 0
% 0.21/0.47  # Backward-subsumed                    : 8
% 0.21/0.47  # Backward-rewritten                   : 4
% 0.21/0.47  # Generated clauses                    : 3501
% 0.21/0.47  # ...of the previous two non-trivial   : 2674
% 0.21/0.47  # Contextual simplify-reflections      : 0
% 0.21/0.47  # Paramodulations                      : 3248
% 0.21/0.47  # Factorizations                       : 6
% 0.21/0.47  # Equation resolutions                 : 248
% 0.21/0.47  # Propositional unsat checks           : 0
% 0.21/0.47  #    Propositional check models        : 0
% 0.21/0.47  #    Propositional check unsatisfiable : 0
% 0.21/0.47  #    Propositional clauses             : 0
% 0.21/0.47  #    Propositional clauses after purity: 0
% 0.21/0.47  #    Propositional unsat core size     : 0
% 0.21/0.47  #    Propositional preprocessing time  : 0.000
% 0.21/0.47  #    Propositional encoding time       : 0.000
% 0.21/0.47  #    Propositional solver time         : 0.000
% 0.21/0.47  #    Success case prop preproc time    : 0.000
% 0.21/0.47  #    Success case prop encoding time   : 0.000
% 0.21/0.47  #    Success case prop solver time     : 0.000
% 0.21/0.47  # Current number of processed clauses  : 182
% 0.21/0.47  #    Positive orientable unit clauses  : 19
% 0.21/0.47  #    Positive unorientable unit clauses: 0
% 0.21/0.47  #    Negative unit clauses             : 10
% 0.21/0.47  #    Non-unit-clauses                  : 153
% 0.21/0.47  # Current number of unprocessed clauses: 2299
% 0.21/0.47  # ...number of literals in the above   : 9041
% 0.21/0.47  # Current number of archived formulas  : 0
% 0.21/0.47  # Current number of archived clauses   : 55
% 0.21/0.47  # Clause-clause subsumption calls (NU) : 2309
% 0.21/0.47  # Rec. Clause-clause subsumption calls : 1354
% 0.21/0.47  # Non-unit clause-clause subsumptions  : 122
% 0.21/0.47  # Unit Clause-clause subsumption calls : 103
% 0.21/0.47  # Rewrite failures with RHS unbound    : 0
% 0.21/0.47  # BW rewrite match attempts            : 23
% 0.21/0.47  # BW rewrite match successes           : 4
% 0.21/0.47  # Condensation attempts                : 0
% 0.21/0.47  # Condensation successes               : 0
% 0.21/0.47  # Termbank termtop insertions          : 51699
% 0.21/0.47  
% 0.21/0.47  # -------------------------------------------------
% 0.21/0.47  # User time                : 0.121 s
% 0.21/0.47  # System time              : 0.011 s
% 0.21/0.47  # Total time               : 0.133 s
% 0.21/0.47  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
