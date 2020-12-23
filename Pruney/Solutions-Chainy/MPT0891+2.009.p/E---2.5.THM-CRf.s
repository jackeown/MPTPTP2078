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
% DateTime   : Thu Dec  3 10:59:53 EST 2020

% Result     : Theorem 6.00s
% Output     : CNFRefutation 6.00s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 570 expanded)
%              Number of clauses        :   63 ( 239 expanded)
%              Number of leaves         :   17 ( 143 expanded)
%              Depth                    :   14
%              Number of atoms          :  297 (2126 expanded)
%              Number of equality atoms :  207 (1658 expanded)
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

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t20_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

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

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

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

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t72_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    <=> ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(c_0_17,negated_conjecture,(
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

fof(c_0_18,plain,(
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

fof(c_0_19,plain,(
    ! [X42,X43,X44] : k3_zfmisc_1(X42,X43,X44) = k2_zfmisc_1(k2_zfmisc_1(X42,X43),X44) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_20,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    & esk5_0 != k1_xboole_0
    & esk6_0 != k1_xboole_0
    & m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
    & ( esk7_0 = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
      | esk7_0 = k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
      | esk7_0 = k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_21,plain,(
    ! [X33,X34,X35] :
      ( ( r2_hidden(X33,X34)
        | ~ r2_hidden(X33,k4_xboole_0(X34,k1_tarski(X35))) )
      & ( X33 != X35
        | ~ r2_hidden(X33,k4_xboole_0(X34,k1_tarski(X35))) )
      & ( ~ r2_hidden(X33,X34)
        | X33 = X35
        | r2_hidden(X33,k4_xboole_0(X34,k1_tarski(X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_22,plain,(
    ! [X30] : k2_tarski(X30,X30) = k1_tarski(X30) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_23,plain,(
    ! [X31,X32] : k1_enumset1(X31,X31,X32) = k2_tarski(X31,X32) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_24,plain,(
    ! [X45,X46,X47] :
      ( ( X45 != k1_mcart_1(X45)
        | X45 != k4_tarski(X46,X47) )
      & ( X45 != k2_mcart_1(X45)
        | X45 != k4_tarski(X46,X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).

fof(c_0_25,plain,(
    ! [X53,X54,X55,X56] :
      ( X53 = k1_xboole_0
      | X54 = k1_xboole_0
      | X55 = k1_xboole_0
      | ~ m1_subset_1(X56,k3_zfmisc_1(X53,X54,X55))
      | X56 = k3_mcart_1(k5_mcart_1(X53,X54,X55,X56),k6_mcart_1(X53,X54,X55,X56),k7_mcart_1(X53,X54,X55,X56)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).

fof(c_0_26,plain,(
    ! [X39,X40,X41] : k3_mcart_1(X39,X40,X41) = k4_tarski(k4_tarski(X39,X40),X41) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_27,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( X1 != k2_mcart_1(X1)
    | X1 != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_34,plain,(
    ! [X61,X62] :
      ( k1_mcart_1(k4_tarski(X61,X62)) = X61
      & k2_mcart_1(k4_tarski(X61,X62)) = X62 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk7_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_40,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_41,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_42,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_enumset1(X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

fof(c_0_43,plain,(
    ! [X18] : k4_xboole_0(k1_xboole_0,X18) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_44,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) != k4_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_28])).

cnf(c_0_47,negated_conjecture,
    ( k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = k2_mcart_1(esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k1_enumset1(X1,X1,X1))) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_50,plain,(
    ! [X48,X50,X51,X52] :
      ( ( r2_hidden(esk3_1(X48),X48)
        | X48 = k1_xboole_0 )
      & ( ~ r2_hidden(X50,X48)
        | esk3_1(X48) != k3_mcart_1(X50,X51,X52)
        | X48 = k1_xboole_0 )
      & ( ~ r2_hidden(X51,X48)
        | esk3_1(X48) != k3_mcart_1(X50,X51,X52)
        | X48 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).

fof(c_0_51,plain,(
    ! [X19,X20,X21,X22,X23,X24,X25,X26,X27,X28] :
      ( ( ~ r2_hidden(X23,X22)
        | X23 = X19
        | X23 = X20
        | X23 = X21
        | X22 != k1_enumset1(X19,X20,X21) )
      & ( X24 != X19
        | r2_hidden(X24,X22)
        | X22 != k1_enumset1(X19,X20,X21) )
      & ( X24 != X20
        | r2_hidden(X24,X22)
        | X22 != k1_enumset1(X19,X20,X21) )
      & ( X24 != X21
        | r2_hidden(X24,X22)
        | X22 != k1_enumset1(X19,X20,X21) )
      & ( esk2_4(X25,X26,X27,X28) != X25
        | ~ r2_hidden(esk2_4(X25,X26,X27,X28),X28)
        | X28 = k1_enumset1(X25,X26,X27) )
      & ( esk2_4(X25,X26,X27,X28) != X26
        | ~ r2_hidden(esk2_4(X25,X26,X27,X28),X28)
        | X28 = k1_enumset1(X25,X26,X27) )
      & ( esk2_4(X25,X26,X27,X28) != X27
        | ~ r2_hidden(esk2_4(X25,X26,X27,X28),X28)
        | X28 = k1_enumset1(X25,X26,X27) )
      & ( r2_hidden(esk2_4(X25,X26,X27,X28),X28)
        | esk2_4(X25,X26,X27,X28) = X25
        | esk2_4(X25,X26,X27,X28) = X26
        | esk2_4(X25,X26,X27,X28) = X27
        | X28 = k1_enumset1(X25,X26,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_52,negated_conjecture,
    ( esk7_0 = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
    | esk7_0 = k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
    | esk7_0 = k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_53,plain,
    ( k4_tarski(X1,X2) != X2 ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( k4_tarski(k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)),k2_mcart_1(esk7_0)) = esk7_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_38]),c_0_47]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_58,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( r2_hidden(X9,X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k3_xboole_0(X6,X7) )
      & ( r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k3_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X6)
        | ~ r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k3_xboole_0(X6,X7) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X11)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X12)
        | X13 = k3_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k3_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X12)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k3_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_59,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_60,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_61,negated_conjecture,
    ( k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0
    | k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0
    | k2_mcart_1(esk7_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_47])).

cnf(c_0_62,negated_conjecture,
    ( k2_mcart_1(esk7_0) != esk7_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_63,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_64,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_57])])).

cnf(c_0_66,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_67,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_68,plain,(
    ! [X15] : k4_xboole_0(X15,k1_xboole_0) = X15 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_69,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk3_1(X2) != k3_mcart_1(X3,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_70,negated_conjecture,
    ( k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)) = k1_mcart_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_54])).

cnf(c_0_71,negated_conjecture,
    ( k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0
    | k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0 ),
    inference(sr,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_72,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k1_enumset1(X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_73,plain,
    ( r2_hidden(esk3_1(k1_enumset1(X1,X2,X3)),k1_enumset1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

fof(c_0_74,plain,(
    ! [X36,X37,X38] :
      ( ( ~ r2_hidden(X36,X38)
        | k4_xboole_0(k2_tarski(X36,X37),X38) != k2_tarski(X36,X37) )
      & ( ~ r2_hidden(X37,X38)
        | k4_xboole_0(k2_tarski(X36,X37),X38) != k2_tarski(X36,X37) )
      & ( r2_hidden(X36,X38)
        | r2_hidden(X37,X38)
        | k4_xboole_0(k2_tarski(X36,X37),X38) = k2_tarski(X36,X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).

cnf(c_0_75,plain,
    ( X3 = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_76,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_77,plain,
    ( X2 = k1_xboole_0
    | esk3_1(X2) != k4_tarski(k4_tarski(X3,X1),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_69,c_0_36])).

cnf(c_0_78,negated_conjecture,
    ( k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),esk7_0) = k1_mcart_1(esk7_0)
    | k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_79,plain,
    ( esk3_1(k1_enumset1(X1,X2,X3)) = X3
    | esk3_1(k1_enumset1(X1,X2,X3)) = X2
    | esk3_1(k1_enumset1(X1,X2,X3)) = X1 ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_80,plain,
    ( ~ r2_hidden(X1,X2)
    | k4_xboole_0(k2_tarski(X3,X1),X2) != k2_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_81,plain,
    ( X1 = k4_xboole_0(X2,X2)
    | r2_hidden(esk1_3(X2,k1_xboole_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_55])).

cnf(c_0_82,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk3_1(X2) != k3_mcart_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_83,negated_conjecture,
    ( k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0
    | X1 = k1_xboole_0
    | esk3_1(X1) != k4_tarski(k1_mcart_1(esk7_0),X2)
    | ~ r2_hidden(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk7_0),k2_mcart_1(esk7_0)) = esk7_0 ),
    inference(rw,[status(thm)],[c_0_54,c_0_70])).

cnf(c_0_85,plain,
    ( esk3_1(k1_enumset1(X1,X2,X2)) = X1
    | esk3_1(k1_enumset1(X1,X2,X2)) = X2 ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_79])])).

cnf(c_0_86,plain,
    ( k4_xboole_0(k1_enumset1(X3,X3,X1),X2) != k1_enumset1(X3,X3,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_32]),c_0_32])).

cnf(c_0_87,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_81]),c_0_49]),c_0_49]),c_0_55])).

cnf(c_0_88,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_89,plain,
    ( X2 = k1_xboole_0
    | esk3_1(X2) != k4_tarski(k4_tarski(X1,X3),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_82,c_0_36])).

cnf(c_0_90,negated_conjecture,
    ( k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0
    | X1 = k1_xboole_0
    | esk3_1(X1) != esk7_0
    | ~ r2_hidden(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_91,plain,
    ( esk3_1(k1_enumset1(X1,X1,X1)) = X1 ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_85])])).

cnf(c_0_92,plain,
    ( k1_enumset1(X1,X1,X2) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_65])])).

cnf(c_0_93,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_88])])).

cnf(c_0_94,negated_conjecture,
    ( X1 = k1_xboole_0
    | esk3_1(X1) != esk7_0
    | ~ r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_54])).

cnf(c_0_95,negated_conjecture,
    ( k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_92])]),c_0_93])])).

cnf(c_0_96,negated_conjecture,
    ( X1 = k1_xboole_0
    | esk3_1(X1) != esk7_0
    | ~ r2_hidden(esk7_0,X1) ),
    inference(rw,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_91]),c_0_92])]),c_0_93])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:22:55 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 6.00/6.16  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 6.00/6.16  # and selection function SelectNegativeLiterals.
% 6.00/6.16  #
% 6.00/6.16  # Preprocessing time       : 0.029 s
% 6.00/6.16  # Presaturation interreduction done
% 6.00/6.16  
% 6.00/6.16  # Proof found!
% 6.00/6.16  # SZS status Theorem
% 6.00/6.16  # SZS output start CNFRefutation
% 6.00/6.16  fof(t51_mcart_1, conjecture, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_mcart_1)).
% 6.00/6.16  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 6.00/6.16  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 6.00/6.16  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 6.00/6.16  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.00/6.16  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.00/6.16  fof(t20_mcart_1, axiom, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 6.00/6.16  fof(t48_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 6.00/6.16  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 6.00/6.16  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 6.00/6.16  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 6.00/6.16  fof(t29_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k3_mcart_1(X3,X4,X5))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 6.00/6.16  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 6.00/6.16  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 6.00/6.16  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.00/6.16  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 6.00/6.16  fof(t72_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)<=>(~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 6.00/6.16  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4))))))), inference(assume_negation,[status(cth)],[t51_mcart_1])).
% 6.00/6.16  fof(c_0_18, plain, ![X57, X58, X59, X60]:(((k5_mcart_1(X57,X58,X59,X60)=k1_mcart_1(k1_mcart_1(X60))|~m1_subset_1(X60,k3_zfmisc_1(X57,X58,X59))|(X57=k1_xboole_0|X58=k1_xboole_0|X59=k1_xboole_0))&(k6_mcart_1(X57,X58,X59,X60)=k2_mcart_1(k1_mcart_1(X60))|~m1_subset_1(X60,k3_zfmisc_1(X57,X58,X59))|(X57=k1_xboole_0|X58=k1_xboole_0|X59=k1_xboole_0)))&(k7_mcart_1(X57,X58,X59,X60)=k2_mcart_1(X60)|~m1_subset_1(X60,k3_zfmisc_1(X57,X58,X59))|(X57=k1_xboole_0|X58=k1_xboole_0|X59=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 6.00/6.16  fof(c_0_19, plain, ![X42, X43, X44]:k3_zfmisc_1(X42,X43,X44)=k2_zfmisc_1(k2_zfmisc_1(X42,X43),X44), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 6.00/6.16  fof(c_0_20, negated_conjecture, (((esk4_0!=k1_xboole_0&esk5_0!=k1_xboole_0)&esk6_0!=k1_xboole_0)&(m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))&(esk7_0=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|esk7_0=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|esk7_0=k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 6.00/6.16  fof(c_0_21, plain, ![X33, X34, X35]:(((r2_hidden(X33,X34)|~r2_hidden(X33,k4_xboole_0(X34,k1_tarski(X35))))&(X33!=X35|~r2_hidden(X33,k4_xboole_0(X34,k1_tarski(X35)))))&(~r2_hidden(X33,X34)|X33=X35|r2_hidden(X33,k4_xboole_0(X34,k1_tarski(X35))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 6.00/6.16  fof(c_0_22, plain, ![X30]:k2_tarski(X30,X30)=k1_tarski(X30), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 6.00/6.16  fof(c_0_23, plain, ![X31, X32]:k1_enumset1(X31,X31,X32)=k2_tarski(X31,X32), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 6.00/6.16  fof(c_0_24, plain, ![X45, X46, X47]:((X45!=k1_mcart_1(X45)|X45!=k4_tarski(X46,X47))&(X45!=k2_mcart_1(X45)|X45!=k4_tarski(X46,X47))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).
% 6.00/6.16  fof(c_0_25, plain, ![X53, X54, X55, X56]:(X53=k1_xboole_0|X54=k1_xboole_0|X55=k1_xboole_0|(~m1_subset_1(X56,k3_zfmisc_1(X53,X54,X55))|X56=k3_mcart_1(k5_mcart_1(X53,X54,X55,X56),k6_mcart_1(X53,X54,X55,X56),k7_mcart_1(X53,X54,X55,X56)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).
% 6.00/6.16  fof(c_0_26, plain, ![X39, X40, X41]:k3_mcart_1(X39,X40,X41)=k4_tarski(k4_tarski(X39,X40),X41), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 6.00/6.16  cnf(c_0_27, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 6.00/6.16  cnf(c_0_28, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 6.00/6.16  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 6.00/6.16  cnf(c_0_30, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 6.00/6.16  cnf(c_0_31, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 6.00/6.16  cnf(c_0_32, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 6.00/6.16  cnf(c_0_33, plain, (X1!=k2_mcart_1(X1)|X1!=k4_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 6.00/6.16  fof(c_0_34, plain, ![X61, X62]:(k1_mcart_1(k4_tarski(X61,X62))=X61&k2_mcart_1(k4_tarski(X61,X62))=X62), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 6.00/6.16  cnf(c_0_35, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 6.00/6.16  cnf(c_0_36, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 6.00/6.16  cnf(c_0_37, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 6.00/6.16  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk7_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[c_0_29, c_0_28])).
% 6.00/6.16  cnf(c_0_39, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 6.00/6.16  cnf(c_0_40, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 6.00/6.16  cnf(c_0_41, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 6.00/6.16  cnf(c_0_42, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_enumset1(X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 6.00/6.16  fof(c_0_43, plain, ![X18]:k4_xboole_0(k1_xboole_0,X18)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 6.00/6.16  cnf(c_0_44, plain, (k2_mcart_1(k4_tarski(X1,X2))!=k4_tarski(X1,X2)), inference(er,[status(thm)],[c_0_33])).
% 6.00/6.16  cnf(c_0_45, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_34])).
% 6.00/6.16  cnf(c_0_46, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X4=k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_28])).
% 6.00/6.16  cnf(c_0_47, negated_conjecture, (k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=k2_mcart_1(esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40]), c_0_41])).
% 6.00/6.16  cnf(c_0_48, plain, (~r2_hidden(X1,k4_xboole_0(X2,k1_enumset1(X1,X1,X1)))), inference(er,[status(thm)],[c_0_42])).
% 6.00/6.16  cnf(c_0_49, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_43])).
% 6.00/6.16  fof(c_0_50, plain, ![X48, X50, X51, X52]:((r2_hidden(esk3_1(X48),X48)|X48=k1_xboole_0)&((~r2_hidden(X50,X48)|esk3_1(X48)!=k3_mcart_1(X50,X51,X52)|X48=k1_xboole_0)&(~r2_hidden(X51,X48)|esk3_1(X48)!=k3_mcart_1(X50,X51,X52)|X48=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).
% 6.00/6.16  fof(c_0_51, plain, ![X19, X20, X21, X22, X23, X24, X25, X26, X27, X28]:(((~r2_hidden(X23,X22)|(X23=X19|X23=X20|X23=X21)|X22!=k1_enumset1(X19,X20,X21))&(((X24!=X19|r2_hidden(X24,X22)|X22!=k1_enumset1(X19,X20,X21))&(X24!=X20|r2_hidden(X24,X22)|X22!=k1_enumset1(X19,X20,X21)))&(X24!=X21|r2_hidden(X24,X22)|X22!=k1_enumset1(X19,X20,X21))))&((((esk2_4(X25,X26,X27,X28)!=X25|~r2_hidden(esk2_4(X25,X26,X27,X28),X28)|X28=k1_enumset1(X25,X26,X27))&(esk2_4(X25,X26,X27,X28)!=X26|~r2_hidden(esk2_4(X25,X26,X27,X28),X28)|X28=k1_enumset1(X25,X26,X27)))&(esk2_4(X25,X26,X27,X28)!=X27|~r2_hidden(esk2_4(X25,X26,X27,X28),X28)|X28=k1_enumset1(X25,X26,X27)))&(r2_hidden(esk2_4(X25,X26,X27,X28),X28)|(esk2_4(X25,X26,X27,X28)=X25|esk2_4(X25,X26,X27,X28)=X26|esk2_4(X25,X26,X27,X28)=X27)|X28=k1_enumset1(X25,X26,X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 6.00/6.16  cnf(c_0_52, negated_conjecture, (esk7_0=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|esk7_0=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|esk7_0=k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 6.00/6.16  cnf(c_0_53, plain, (k4_tarski(X1,X2)!=X2), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 6.00/6.16  cnf(c_0_54, negated_conjecture, (k4_tarski(k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)),k2_mcart_1(esk7_0))=esk7_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_38]), c_0_47]), c_0_39]), c_0_40]), c_0_41])).
% 6.00/6.16  cnf(c_0_55, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 6.00/6.16  cnf(c_0_56, plain, (r2_hidden(esk3_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_50])).
% 6.00/6.16  cnf(c_0_57, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 6.00/6.16  fof(c_0_58, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k3_xboole_0(X6,X7))&(r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k3_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|~r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k3_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|~r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k3_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k3_xboole_0(X11,X12))&(r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k3_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 6.00/6.16  fof(c_0_59, plain, ![X16, X17]:k4_xboole_0(X16,k4_xboole_0(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 6.00/6.16  cnf(c_0_60, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 6.00/6.16  cnf(c_0_61, negated_conjecture, (k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0|k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0|k2_mcart_1(esk7_0)=esk7_0), inference(spm,[status(thm)],[c_0_52, c_0_47])).
% 6.00/6.16  cnf(c_0_62, negated_conjecture, (k2_mcart_1(esk7_0)!=esk7_0), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 6.00/6.16  cnf(c_0_63, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 6.00/6.16  cnf(c_0_64, plain, (r2_hidden(esk3_1(X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 6.00/6.16  cnf(c_0_65, plain, (r2_hidden(X1,k1_enumset1(X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_57])])).
% 6.00/6.16  cnf(c_0_66, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 6.00/6.16  cnf(c_0_67, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 6.00/6.16  fof(c_0_68, plain, ![X15]:k4_xboole_0(X15,k1_xboole_0)=X15, inference(variable_rename,[status(thm)],[t3_boole])).
% 6.00/6.16  cnf(c_0_69, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk3_1(X2)!=k3_mcart_1(X3,X1,X4)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 6.00/6.16  cnf(c_0_70, negated_conjecture, (k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0))=k1_mcart_1(esk7_0)), inference(spm,[status(thm)],[c_0_60, c_0_54])).
% 6.00/6.16  cnf(c_0_71, negated_conjecture, (k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0|k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0), inference(sr,[status(thm)],[c_0_61, c_0_62])).
% 6.00/6.16  cnf(c_0_72, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k1_enumset1(X4,X3,X2))), inference(er,[status(thm)],[c_0_63])).
% 6.00/6.16  cnf(c_0_73, plain, (r2_hidden(esk3_1(k1_enumset1(X1,X2,X3)),k1_enumset1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 6.00/6.16  fof(c_0_74, plain, ![X36, X37, X38]:(((~r2_hidden(X36,X38)|k4_xboole_0(k2_tarski(X36,X37),X38)!=k2_tarski(X36,X37))&(~r2_hidden(X37,X38)|k4_xboole_0(k2_tarski(X36,X37),X38)!=k2_tarski(X36,X37)))&(r2_hidden(X36,X38)|r2_hidden(X37,X38)|k4_xboole_0(k2_tarski(X36,X37),X38)=k2_tarski(X36,X37))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).
% 6.00/6.16  cnf(c_0_75, plain, (X3=k4_xboole_0(X1,k4_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_66, c_0_67])).
% 6.00/6.16  cnf(c_0_76, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_68])).
% 6.00/6.16  cnf(c_0_77, plain, (X2=k1_xboole_0|esk3_1(X2)!=k4_tarski(k4_tarski(X3,X1),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_69, c_0_36])).
% 6.00/6.16  cnf(c_0_78, negated_conjecture, (k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),esk7_0)=k1_mcart_1(esk7_0)|k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 6.00/6.16  cnf(c_0_79, plain, (esk3_1(k1_enumset1(X1,X2,X3))=X3|esk3_1(k1_enumset1(X1,X2,X3))=X2|esk3_1(k1_enumset1(X1,X2,X3))=X1), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 6.00/6.16  cnf(c_0_80, plain, (~r2_hidden(X1,X2)|k4_xboole_0(k2_tarski(X3,X1),X2)!=k2_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 6.00/6.16  cnf(c_0_81, plain, (X1=k4_xboole_0(X2,X2)|r2_hidden(esk1_3(X2,k1_xboole_0,X1),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_55])).
% 6.00/6.16  cnf(c_0_82, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk3_1(X2)!=k3_mcart_1(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 6.00/6.16  cnf(c_0_83, negated_conjecture, (k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0|X1=k1_xboole_0|esk3_1(X1)!=k4_tarski(k1_mcart_1(esk7_0),X2)|~r2_hidden(esk7_0,X1)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 6.00/6.16  cnf(c_0_84, negated_conjecture, (k4_tarski(k1_mcart_1(esk7_0),k2_mcart_1(esk7_0))=esk7_0), inference(rw,[status(thm)],[c_0_54, c_0_70])).
% 6.00/6.16  cnf(c_0_85, plain, (esk3_1(k1_enumset1(X1,X2,X2))=X1|esk3_1(k1_enumset1(X1,X2,X2))=X2), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_79])])).
% 6.00/6.16  cnf(c_0_86, plain, (k4_xboole_0(k1_enumset1(X3,X3,X1),X2)!=k1_enumset1(X3,X3,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_32]), c_0_32])).
% 6.00/6.16  cnf(c_0_87, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_81]), c_0_49]), c_0_49]), c_0_55])).
% 6.00/6.16  cnf(c_0_88, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 6.00/6.16  cnf(c_0_89, plain, (X2=k1_xboole_0|esk3_1(X2)!=k4_tarski(k4_tarski(X1,X3),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_82, c_0_36])).
% 6.00/6.16  cnf(c_0_90, negated_conjecture, (k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0|X1=k1_xboole_0|esk3_1(X1)!=esk7_0|~r2_hidden(esk7_0,X1)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 6.00/6.16  cnf(c_0_91, plain, (esk3_1(k1_enumset1(X1,X1,X1))=X1), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_85])])).
% 6.00/6.16  cnf(c_0_92, plain, (k1_enumset1(X1,X1,X2)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_65])])).
% 6.00/6.16  cnf(c_0_93, plain, (r2_hidden(X1,k1_enumset1(X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_88])])).
% 6.00/6.16  cnf(c_0_94, negated_conjecture, (X1=k1_xboole_0|esk3_1(X1)!=esk7_0|~r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),X1)), inference(spm,[status(thm)],[c_0_89, c_0_54])).
% 6.00/6.16  cnf(c_0_95, negated_conjecture, (k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_92])]), c_0_93])])).
% 6.00/6.16  cnf(c_0_96, negated_conjecture, (X1=k1_xboole_0|esk3_1(X1)!=esk7_0|~r2_hidden(esk7_0,X1)), inference(rw,[status(thm)],[c_0_94, c_0_95])).
% 6.00/6.16  cnf(c_0_97, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_91]), c_0_92])]), c_0_93])]), ['proof']).
% 6.00/6.16  # SZS output end CNFRefutation
% 6.00/6.16  # Proof object total steps             : 98
% 6.00/6.16  # Proof object clause steps            : 63
% 6.00/6.16  # Proof object formula steps           : 35
% 6.00/6.16  # Proof object conjectures             : 23
% 6.00/6.16  # Proof object clause conjectures      : 20
% 6.00/6.16  # Proof object formula conjectures     : 3
% 6.00/6.16  # Proof object initial clauses used    : 26
% 6.00/6.16  # Proof object initial formulas used   : 17
% 6.00/6.16  # Proof object generating inferences   : 20
% 6.00/6.16  # Proof object simplifying inferences  : 45
% 6.00/6.16  # Training examples: 0 positive, 0 negative
% 6.00/6.16  # Parsed axioms                        : 17
% 6.00/6.16  # Removed by relevancy pruning/SinE    : 0
% 6.00/6.16  # Initial clauses                      : 43
% 6.00/6.16  # Removed in clause preprocessing      : 5
% 6.00/6.16  # Initial clauses in saturation        : 38
% 6.00/6.16  # Processed clauses                    : 9328
% 6.00/6.16  # ...of these trivial                  : 348
% 6.00/6.16  # ...subsumed                          : 7328
% 6.00/6.16  # ...remaining for further processing  : 1652
% 6.00/6.16  # Other redundant clauses eliminated   : 49331
% 6.00/6.16  # Clauses deleted for lack of memory   : 0
% 6.00/6.16  # Backward-subsumed                    : 56
% 6.00/6.16  # Backward-rewritten                   : 109
% 6.00/6.16  # Generated clauses                    : 771867
% 6.00/6.16  # ...of the previous two non-trivial   : 660619
% 6.00/6.16  # Contextual simplify-reflections      : 32
% 6.00/6.16  # Paramodulations                      : 722438
% 6.00/6.16  # Factorizations                       : 94
% 6.00/6.16  # Equation resolutions                 : 49337
% 6.00/6.16  # Propositional unsat checks           : 0
% 6.00/6.16  #    Propositional check models        : 0
% 6.00/6.16  #    Propositional check unsatisfiable : 0
% 6.00/6.16  #    Propositional clauses             : 0
% 6.00/6.16  #    Propositional clauses after purity: 0
% 6.00/6.16  #    Propositional unsat core size     : 0
% 6.00/6.16  #    Propositional preprocessing time  : 0.000
% 6.00/6.16  #    Propositional encoding time       : 0.000
% 6.00/6.16  #    Propositional solver time         : 0.000
% 6.00/6.16  #    Success case prop preproc time    : 0.000
% 6.00/6.16  #    Success case prop encoding time   : 0.000
% 6.00/6.16  #    Success case prop solver time     : 0.000
% 6.00/6.16  # Current number of processed clauses  : 1438
% 6.00/6.16  #    Positive orientable unit clauses  : 96
% 6.00/6.16  #    Positive unorientable unit clauses: 0
% 6.00/6.16  #    Negative unit clauses             : 11
% 6.00/6.16  #    Non-unit-clauses                  : 1331
% 6.00/6.16  # Current number of unprocessed clauses: 650661
% 6.00/6.16  # ...number of literals in the above   : 3135372
% 6.00/6.16  # Current number of archived formulas  : 0
% 6.00/6.16  # Current number of archived clauses   : 209
% 6.00/6.16  # Clause-clause subsumption calls (NU) : 276493
% 6.00/6.16  # Rec. Clause-clause subsumption calls : 150598
% 6.00/6.16  # Non-unit clause-clause subsumptions  : 6452
% 6.00/6.16  # Unit Clause-clause subsumption calls : 3643
% 6.00/6.16  # Rewrite failures with RHS unbound    : 0
% 6.00/6.16  # BW rewrite match attempts            : 418
% 6.00/6.16  # BW rewrite match successes           : 25
% 6.00/6.16  # Condensation attempts                : 0
% 6.00/6.16  # Condensation successes               : 0
% 6.00/6.16  # Termbank termtop insertions          : 16778921
% 6.00/6.19  
% 6.00/6.19  # -------------------------------------------------
% 6.00/6.19  # User time                : 5.577 s
% 6.00/6.19  # System time              : 0.267 s
% 6.00/6.19  # Total time               : 5.844 s
% 6.00/6.19  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
