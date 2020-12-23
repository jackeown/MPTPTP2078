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
% DateTime   : Thu Dec  3 10:59:55 EST 2020

% Result     : Theorem 3.86s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :   79 (1713 expanded)
%              Number of clauses        :   58 ( 729 expanded)
%              Number of leaves         :   10 ( 418 expanded)
%              Depth                    :   18
%              Number of atoms          :  231 (6345 expanded)
%              Number of equality atoms :  150 (5068 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
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

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t20_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

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

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(c_0_10,negated_conjecture,(
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

fof(c_0_11,plain,(
    ! [X43,X44,X45,X46] :
      ( X43 = k1_xboole_0
      | X44 = k1_xboole_0
      | X45 = k1_xboole_0
      | ~ m1_subset_1(X46,k3_zfmisc_1(X43,X44,X45))
      | X46 = k3_mcart_1(k5_mcart_1(X43,X44,X45,X46),k6_mcart_1(X43,X44,X45,X46),k7_mcart_1(X43,X44,X45,X46)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).

fof(c_0_12,plain,(
    ! [X29,X30,X31] : k3_mcart_1(X29,X30,X31) = k4_tarski(k4_tarski(X29,X30),X31) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_13,plain,(
    ! [X32,X33,X34] : k3_zfmisc_1(X32,X33,X34) = k2_zfmisc_1(k2_zfmisc_1(X32,X33),X34) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_14,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    & esk5_0 != k1_xboole_0
    & esk6_0 != k1_xboole_0
    & m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
    & ( esk7_0 = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
      | esk7_0 = k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
      | esk7_0 = k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_15,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X35,X36,X37] :
      ( ( X35 != k1_mcart_1(X35)
        | X35 != k4_tarski(X36,X37) )
      & ( X35 != k2_mcart_1(X35)
        | X35 != k4_tarski(X36,X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).

fof(c_0_20,plain,(
    ! [X47,X48] :
      ( k1_mcart_1(k4_tarski(X47,X48)) = X47
      & k2_mcart_1(k4_tarski(X47,X48)) = X48 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_21,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk7_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,plain,
    ( X1 != k2_mcart_1(X1)
    | X1 != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( k4_tarski(k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)),k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)) = esk7_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_29,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) != k4_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_26])).

fof(c_0_30,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22] :
      ( ( ~ r2_hidden(X18,X17)
        | X18 = X15
        | X18 = X16
        | X17 != k2_tarski(X15,X16) )
      & ( X19 != X15
        | r2_hidden(X19,X17)
        | X17 != k2_tarski(X15,X16) )
      & ( X19 != X16
        | r2_hidden(X19,X17)
        | X17 != k2_tarski(X15,X16) )
      & ( esk2_3(X20,X21,X22) != X20
        | ~ r2_hidden(esk2_3(X20,X21,X22),X22)
        | X22 = k2_tarski(X20,X21) )
      & ( esk2_3(X20,X21,X22) != X21
        | ~ r2_hidden(esk2_3(X20,X21,X22),X22)
        | X22 = k2_tarski(X20,X21) )
      & ( r2_hidden(esk2_3(X20,X21,X22),X22)
        | esk2_3(X20,X21,X22) = X20
        | esk2_3(X20,X21,X22) = X21
        | X22 = k2_tarski(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_31,plain,(
    ! [X24,X25] : k1_enumset1(X24,X24,X25) = k2_tarski(X24,X25) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_32,negated_conjecture,
    ( k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = k2_mcart_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( k4_tarski(X1,X2) != X2 ),
    inference(rw,[status(thm)],[c_0_29,c_0_27])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_36,plain,(
    ! [X38,X40,X41,X42] :
      ( ( r2_hidden(esk3_1(X38),X38)
        | X38 = k1_xboole_0 )
      & ( ~ r2_hidden(X40,X38)
        | esk3_1(X38) != k3_mcart_1(X40,X41,X42)
        | X38 = k1_xboole_0 )
      & ( ~ r2_hidden(X41,X38)
        | esk3_1(X38) != k3_mcart_1(X40,X41,X42)
        | X38 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).

cnf(c_0_37,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_38,negated_conjecture,
    ( k4_tarski(k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)),k2_mcart_1(esk7_0)) = esk7_0 ),
    inference(rw,[status(thm)],[c_0_28,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( esk7_0 = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
    | esk7_0 = k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
    | esk7_0 = k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_40,negated_conjecture,
    ( k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) != esk7_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_28])).

cnf(c_0_41,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X4,X2) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk3_1(X2) != k3_mcart_1(X3,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)) = k1_mcart_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0
    | k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0 ),
    inference(sr,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k1_enumset1(X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_41,c_0_35])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_42])])).

cnf(c_0_48,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,plain,
    ( X2 = k1_xboole_0
    | esk3_1(X2) != k4_tarski(k4_tarski(X3,X1),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_43,c_0_16])).

cnf(c_0_50,negated_conjecture,
    ( k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),esk7_0) = k1_mcart_1(esk7_0)
    | k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k1_enumset1(X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_52,plain,
    ( r2_hidden(esk3_1(k1_enumset1(X1,X1,X2)),k1_enumset1(X1,X1,X2))
    | r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_54,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk3_1(X2) != k3_mcart_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_55,negated_conjecture,
    ( k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0
    | X1 = k1_xboole_0
    | esk3_1(X1) != k4_tarski(k1_mcart_1(esk7_0),X2)
    | ~ r2_hidden(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk7_0),k2_mcart_1(esk7_0)) = esk7_0 ),
    inference(rw,[status(thm)],[c_0_38,c_0_44])).

cnf(c_0_57,plain,
    ( esk3_1(k1_enumset1(X1,X1,X2)) = X2
    | esk3_1(k1_enumset1(X1,X1,X2)) = X1
    | r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X2,X4) ),
    inference(rw,[status(thm)],[c_0_53,c_0_35])).

cnf(c_0_59,plain,
    ( X2 = k1_xboole_0
    | esk3_1(X2) != k4_tarski(k4_tarski(X1,X3),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_54,c_0_16])).

cnf(c_0_60,negated_conjecture,
    ( k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0
    | X1 = k1_xboole_0
    | esk3_1(X1) != esk7_0
    | ~ r2_hidden(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,plain,
    ( esk3_1(k1_enumset1(X1,X1,X1)) = X1
    | r2_hidden(X1,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_57])])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_58])])).

fof(c_0_63,plain,(
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

cnf(c_0_64,negated_conjecture,
    ( X1 = k1_xboole_0
    | esk3_1(X1) != esk7_0
    | ~ r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_38])).

cnf(c_0_65,negated_conjecture,
    ( k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0
    | k1_enumset1(esk7_0,esk7_0,esk7_0) = k1_xboole_0
    | r2_hidden(esk7_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61])]),c_0_62])])).

cnf(c_0_66,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( k1_enumset1(esk7_0,esk7_0,esk7_0) = k1_xboole_0
    | r2_hidden(esk7_0,k1_xboole_0)
    | ~ r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k1_enumset1(esk7_0,esk7_0,esk7_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_61])])).

cnf(c_0_68,negated_conjecture,
    ( k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0
    | r2_hidden(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_65])).

cnf(c_0_69,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( k1_enumset1(esk7_0,esk7_0,esk7_0) = k1_xboole_0
    | r2_hidden(esk7_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_62])])).

cnf(c_0_71,plain,
    ( r2_hidden(esk3_1(k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))
    | ~ r2_hidden(X3,k1_xboole_0)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_69,c_0_48])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_70])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk3_1(k4_xboole_0(X1,k1_xboole_0)),k4_xboole_0(X1,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_72])])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( ~ r2_hidden(esk3_1(k4_xboole_0(X1,k1_xboole_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk3_1(k4_xboole_0(X1,k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_76,c_0_77]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:30:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 3.86/4.02  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 3.86/4.02  # and selection function SelectNegativeLiterals.
% 3.86/4.02  #
% 3.86/4.02  # Preprocessing time       : 0.052 s
% 3.86/4.02  # Presaturation interreduction done
% 3.86/4.02  
% 3.86/4.02  # Proof found!
% 3.86/4.02  # SZS status Theorem
% 3.86/4.02  # SZS output start CNFRefutation
% 3.86/4.02  fof(t51_mcart_1, conjecture, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_mcart_1)).
% 3.86/4.02  fof(t48_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 3.86/4.02  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 3.86/4.02  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.86/4.02  fof(t20_mcart_1, axiom, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.86/4.02  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.86/4.02  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.86/4.02  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.86/4.02  fof(t29_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k3_mcart_1(X3,X4,X5))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 3.86/4.02  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.86/4.02  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4))))))), inference(assume_negation,[status(cth)],[t51_mcart_1])).
% 3.86/4.02  fof(c_0_11, plain, ![X43, X44, X45, X46]:(X43=k1_xboole_0|X44=k1_xboole_0|X45=k1_xboole_0|(~m1_subset_1(X46,k3_zfmisc_1(X43,X44,X45))|X46=k3_mcart_1(k5_mcart_1(X43,X44,X45,X46),k6_mcart_1(X43,X44,X45,X46),k7_mcart_1(X43,X44,X45,X46)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).
% 3.86/4.02  fof(c_0_12, plain, ![X29, X30, X31]:k3_mcart_1(X29,X30,X31)=k4_tarski(k4_tarski(X29,X30),X31), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 3.86/4.02  fof(c_0_13, plain, ![X32, X33, X34]:k3_zfmisc_1(X32,X33,X34)=k2_zfmisc_1(k2_zfmisc_1(X32,X33),X34), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 3.86/4.02  fof(c_0_14, negated_conjecture, (((esk4_0!=k1_xboole_0&esk5_0!=k1_xboole_0)&esk6_0!=k1_xboole_0)&(m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))&(esk7_0=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|esk7_0=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|esk7_0=k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 3.86/4.02  cnf(c_0_15, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 3.86/4.02  cnf(c_0_16, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 3.86/4.02  cnf(c_0_17, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 3.86/4.02  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.86/4.02  fof(c_0_19, plain, ![X35, X36, X37]:((X35!=k1_mcart_1(X35)|X35!=k4_tarski(X36,X37))&(X35!=k2_mcart_1(X35)|X35!=k4_tarski(X36,X37))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).
% 3.86/4.02  fof(c_0_20, plain, ![X47, X48]:(k1_mcart_1(k4_tarski(X47,X48))=X47&k2_mcart_1(k4_tarski(X47,X48))=X48), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 3.86/4.02  cnf(c_0_21, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X4=k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 3.86/4.02  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk7_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[c_0_18, c_0_17])).
% 3.86/4.02  cnf(c_0_23, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.86/4.02  cnf(c_0_24, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.86/4.02  cnf(c_0_25, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.86/4.02  cnf(c_0_26, plain, (X1!=k2_mcart_1(X1)|X1!=k4_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.86/4.02  cnf(c_0_27, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.86/4.02  cnf(c_0_28, negated_conjecture, (k4_tarski(k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)),k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0))=esk7_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24]), c_0_25])).
% 3.86/4.02  cnf(c_0_29, plain, (k2_mcart_1(k4_tarski(X1,X2))!=k4_tarski(X1,X2)), inference(er,[status(thm)],[c_0_26])).
% 3.86/4.02  fof(c_0_30, plain, ![X15, X16, X17, X18, X19, X20, X21, X22]:(((~r2_hidden(X18,X17)|(X18=X15|X18=X16)|X17!=k2_tarski(X15,X16))&((X19!=X15|r2_hidden(X19,X17)|X17!=k2_tarski(X15,X16))&(X19!=X16|r2_hidden(X19,X17)|X17!=k2_tarski(X15,X16))))&(((esk2_3(X20,X21,X22)!=X20|~r2_hidden(esk2_3(X20,X21,X22),X22)|X22=k2_tarski(X20,X21))&(esk2_3(X20,X21,X22)!=X21|~r2_hidden(esk2_3(X20,X21,X22),X22)|X22=k2_tarski(X20,X21)))&(r2_hidden(esk2_3(X20,X21,X22),X22)|(esk2_3(X20,X21,X22)=X20|esk2_3(X20,X21,X22)=X21)|X22=k2_tarski(X20,X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 3.86/4.02  fof(c_0_31, plain, ![X24, X25]:k1_enumset1(X24,X24,X25)=k2_tarski(X24,X25), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 3.86/4.02  cnf(c_0_32, negated_conjecture, (k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=k2_mcart_1(esk7_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 3.86/4.02  cnf(c_0_33, plain, (k4_tarski(X1,X2)!=X2), inference(rw,[status(thm)],[c_0_29, c_0_27])).
% 3.86/4.02  cnf(c_0_34, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 3.86/4.02  cnf(c_0_35, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.86/4.02  fof(c_0_36, plain, ![X38, X40, X41, X42]:((r2_hidden(esk3_1(X38),X38)|X38=k1_xboole_0)&((~r2_hidden(X40,X38)|esk3_1(X38)!=k3_mcart_1(X40,X41,X42)|X38=k1_xboole_0)&(~r2_hidden(X41,X38)|esk3_1(X38)!=k3_mcart_1(X40,X41,X42)|X38=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).
% 3.86/4.02  cnf(c_0_37, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.86/4.02  cnf(c_0_38, negated_conjecture, (k4_tarski(k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)),k2_mcart_1(esk7_0))=esk7_0), inference(rw,[status(thm)],[c_0_28, c_0_32])).
% 3.86/4.02  cnf(c_0_39, negated_conjecture, (esk7_0=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|esk7_0=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|esk7_0=k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.86/4.02  cnf(c_0_40, negated_conjecture, (k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)!=esk7_0), inference(spm,[status(thm)],[c_0_33, c_0_28])).
% 3.86/4.02  cnf(c_0_41, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 3.86/4.02  cnf(c_0_42, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X4,X2)), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 3.86/4.02  cnf(c_0_43, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk3_1(X2)!=k3_mcart_1(X3,X1,X4)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 3.86/4.02  cnf(c_0_44, negated_conjecture, (k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0))=k1_mcart_1(esk7_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 3.86/4.02  cnf(c_0_45, negated_conjecture, (k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0|k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0), inference(sr,[status(thm)],[c_0_39, c_0_40])).
% 3.86/4.02  cnf(c_0_46, plain, (X1=X4|X1=X3|X2!=k1_enumset1(X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_41, c_0_35])).
% 3.86/4.02  cnf(c_0_47, plain, (r2_hidden(X1,k1_enumset1(X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_42])])).
% 3.86/4.02  cnf(c_0_48, plain, (r2_hidden(esk3_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_36])).
% 3.86/4.02  cnf(c_0_49, plain, (X2=k1_xboole_0|esk3_1(X2)!=k4_tarski(k4_tarski(X3,X1),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_43, c_0_16])).
% 3.86/4.02  cnf(c_0_50, negated_conjecture, (k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),esk7_0)=k1_mcart_1(esk7_0)|k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 3.86/4.02  cnf(c_0_51, plain, (X1=X2|X1=X3|~r2_hidden(X1,k1_enumset1(X3,X3,X2))), inference(er,[status(thm)],[c_0_46])).
% 3.86/4.02  cnf(c_0_52, plain, (r2_hidden(esk3_1(k1_enumset1(X1,X1,X2)),k1_enumset1(X1,X1,X2))|r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 3.86/4.02  cnf(c_0_53, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 3.86/4.02  cnf(c_0_54, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk3_1(X2)!=k3_mcart_1(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 3.86/4.02  cnf(c_0_55, negated_conjecture, (k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0|X1=k1_xboole_0|esk3_1(X1)!=k4_tarski(k1_mcart_1(esk7_0),X2)|~r2_hidden(esk7_0,X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 3.86/4.02  cnf(c_0_56, negated_conjecture, (k4_tarski(k1_mcart_1(esk7_0),k2_mcart_1(esk7_0))=esk7_0), inference(rw,[status(thm)],[c_0_38, c_0_44])).
% 3.86/4.02  cnf(c_0_57, plain, (esk3_1(k1_enumset1(X1,X1,X2))=X2|esk3_1(k1_enumset1(X1,X1,X2))=X1|r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 3.86/4.02  cnf(c_0_58, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X2,X4)), inference(rw,[status(thm)],[c_0_53, c_0_35])).
% 3.86/4.02  cnf(c_0_59, plain, (X2=k1_xboole_0|esk3_1(X2)!=k4_tarski(k4_tarski(X1,X3),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_54, c_0_16])).
% 3.86/4.02  cnf(c_0_60, negated_conjecture, (k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0|X1=k1_xboole_0|esk3_1(X1)!=esk7_0|~r2_hidden(esk7_0,X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 3.86/4.02  cnf(c_0_61, plain, (esk3_1(k1_enumset1(X1,X1,X1))=X1|r2_hidden(X1,k1_xboole_0)), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_57])])).
% 3.86/4.02  cnf(c_0_62, plain, (r2_hidden(X1,k1_enumset1(X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_58])])).
% 3.86/4.02  fof(c_0_63, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7))&(~r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k4_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k4_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))&(~r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 3.86/4.02  cnf(c_0_64, negated_conjecture, (X1=k1_xboole_0|esk3_1(X1)!=esk7_0|~r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),X1)), inference(spm,[status(thm)],[c_0_59, c_0_38])).
% 3.86/4.02  cnf(c_0_65, negated_conjecture, (k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0|k1_enumset1(esk7_0,esk7_0,esk7_0)=k1_xboole_0|r2_hidden(esk7_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61])]), c_0_62])])).
% 3.86/4.02  cnf(c_0_66, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 3.86/4.02  cnf(c_0_67, negated_conjecture, (k1_enumset1(esk7_0,esk7_0,esk7_0)=k1_xboole_0|r2_hidden(esk7_0,k1_xboole_0)|~r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k1_enumset1(esk7_0,esk7_0,esk7_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_61])])).
% 3.86/4.02  cnf(c_0_68, negated_conjecture, (k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0|r2_hidden(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_62, c_0_65])).
% 3.86/4.02  cnf(c_0_69, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_66])).
% 3.86/4.02  cnf(c_0_70, negated_conjecture, (k1_enumset1(esk7_0,esk7_0,esk7_0)=k1_xboole_0|r2_hidden(esk7_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_62])])).
% 3.86/4.02  cnf(c_0_71, plain, (r2_hidden(esk3_1(k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))|~r2_hidden(X3,k1_xboole_0)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_69, c_0_48])).
% 3.86/4.02  cnf(c_0_72, negated_conjecture, (r2_hidden(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_62, c_0_70])).
% 3.86/4.02  cnf(c_0_73, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 3.86/4.02  cnf(c_0_74, negated_conjecture, (r2_hidden(esk3_1(k4_xboole_0(X1,k1_xboole_0)),k4_xboole_0(X1,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_72])])).
% 3.86/4.02  cnf(c_0_75, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_73])).
% 3.86/4.02  cnf(c_0_76, negated_conjecture, (~r2_hidden(esk3_1(k4_xboole_0(X1,k1_xboole_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_69, c_0_74])).
% 3.86/4.02  cnf(c_0_77, negated_conjecture, (r2_hidden(esk3_1(k4_xboole_0(X1,k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_75, c_0_74])).
% 3.86/4.02  cnf(c_0_78, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_76, c_0_77]), ['proof']).
% 3.86/4.02  # SZS output end CNFRefutation
% 3.86/4.02  # Proof object total steps             : 79
% 3.86/4.02  # Proof object clause steps            : 58
% 3.86/4.02  # Proof object formula steps           : 21
% 3.86/4.02  # Proof object conjectures             : 29
% 3.86/4.02  # Proof object clause conjectures      : 26
% 3.86/4.02  # Proof object formula conjectures     : 3
% 3.86/4.02  # Proof object initial clauses used    : 20
% 3.86/4.02  # Proof object initial formulas used   : 10
% 3.86/4.02  # Proof object generating inferences   : 21
% 3.86/4.02  # Proof object simplifying inferences  : 32
% 3.86/4.02  # Training examples: 0 positive, 0 negative
% 3.86/4.02  # Parsed axioms                        : 11
% 3.86/4.02  # Removed by relevancy pruning/SinE    : 0
% 3.86/4.02  # Initial clauses                      : 31
% 3.86/4.02  # Removed in clause preprocessing      : 3
% 3.86/4.02  # Initial clauses in saturation        : 28
% 3.86/4.02  # Processed clauses                    : 7679
% 3.86/4.02  # ...of these trivial                  : 28
% 3.86/4.02  # ...subsumed                          : 4904
% 3.86/4.02  # ...remaining for further processing  : 2747
% 3.86/4.02  # Other redundant clauses eliminated   : 14954
% 3.86/4.02  # Clauses deleted for lack of memory   : 0
% 3.86/4.02  # Backward-subsumed                    : 49
% 3.86/4.02  # Backward-rewritten                   : 28
% 3.86/4.02  # Generated clauses                    : 462788
% 3.86/4.02  # ...of the previous two non-trivial   : 420797
% 3.86/4.02  # Contextual simplify-reflections      : 27
% 3.86/4.02  # Paramodulations                      : 447544
% 3.86/4.02  # Factorizations                       : 285
% 3.86/4.02  # Equation resolutions                 : 14960
% 3.86/4.02  # Propositional unsat checks           : 0
% 3.86/4.02  #    Propositional check models        : 0
% 3.86/4.02  #    Propositional check unsatisfiable : 0
% 3.86/4.02  #    Propositional clauses             : 0
% 3.86/4.02  #    Propositional clauses after purity: 0
% 3.86/4.02  #    Propositional unsat core size     : 0
% 3.86/4.02  #    Propositional preprocessing time  : 0.000
% 3.86/4.02  #    Propositional encoding time       : 0.000
% 3.86/4.02  #    Propositional solver time         : 0.000
% 3.86/4.02  #    Success case prop preproc time    : 0.000
% 3.86/4.02  #    Success case prop encoding time   : 0.000
% 3.86/4.02  #    Success case prop solver time     : 0.000
% 3.86/4.02  # Current number of processed clauses  : 2633
% 3.86/4.02  #    Positive orientable unit clauses  : 46
% 3.86/4.02  #    Positive unorientable unit clauses: 0
% 3.86/4.02  #    Negative unit clauses             : 10
% 3.86/4.02  #    Non-unit-clauses                  : 2577
% 3.86/4.02  # Current number of unprocessed clauses: 412540
% 3.86/4.02  # ...number of literals in the above   : 2434342
% 3.86/4.02  # Current number of archived formulas  : 0
% 3.86/4.02  # Current number of archived clauses   : 109
% 3.86/4.02  # Clause-clause subsumption calls (NU) : 549710
% 3.86/4.02  # Rec. Clause-clause subsumption calls : 123278
% 3.86/4.02  # Non-unit clause-clause subsumptions  : 4474
% 3.86/4.02  # Unit Clause-clause subsumption calls : 5525
% 3.86/4.02  # Rewrite failures with RHS unbound    : 0
% 3.86/4.02  # BW rewrite match attempts            : 162
% 3.86/4.02  # BW rewrite match successes           : 10
% 3.86/4.02  # Condensation attempts                : 0
% 3.86/4.02  # Condensation successes               : 0
% 3.86/4.02  # Termbank termtop insertions          : 11335854
% 3.86/4.04  
% 3.86/4.04  # -------------------------------------------------
% 3.86/4.04  # User time                : 3.523 s
% 3.86/4.04  # System time              : 0.182 s
% 3.86/4.04  # Total time               : 3.705 s
% 3.86/4.04  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
