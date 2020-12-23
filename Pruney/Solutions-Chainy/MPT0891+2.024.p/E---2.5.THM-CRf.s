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
% DateTime   : Thu Dec  3 10:59:56 EST 2020

% Result     : Theorem 0.71s
% Output     : CNFRefutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :  112 (2069 expanded)
%              Number of clauses        :   83 ( 928 expanded)
%              Number of leaves         :   14 ( 498 expanded)
%              Depth                    :   23
%              Number of atoms          :  317 (7793 expanded)
%              Number of equality atoms :  218 (5803 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t72_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    <=> ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

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

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

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

fof(c_0_14,plain,(
    ! [X21,X22,X23] :
      ( ( ~ r2_hidden(X21,X23)
        | k4_xboole_0(k2_tarski(X21,X22),X23) != k2_tarski(X21,X22) )
      & ( ~ r2_hidden(X22,X23)
        | k4_xboole_0(k2_tarski(X21,X22),X23) != k2_tarski(X21,X22) )
      & ( r2_hidden(X21,X23)
        | r2_hidden(X22,X23)
        | k4_xboole_0(k2_tarski(X21,X22),X23) = k2_tarski(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).

fof(c_0_15,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X9,X8)
        | X9 = X6
        | X9 = X7
        | X8 != k2_tarski(X6,X7) )
      & ( X10 != X6
        | r2_hidden(X10,X8)
        | X8 != k2_tarski(X6,X7) )
      & ( X10 != X7
        | r2_hidden(X10,X8)
        | X8 != k2_tarski(X6,X7) )
      & ( esk1_3(X11,X12,X13) != X11
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_tarski(X11,X12) )
      & ( esk1_3(X11,X12,X13) != X12
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_tarski(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X13)
        | esk1_3(X11,X12,X13) = X11
        | esk1_3(X11,X12,X13) = X12
        | X13 = k2_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_17,plain,(
    ! [X17,X18] :
      ( ( k2_zfmisc_1(X17,X18) != k1_xboole_0
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0 )
      & ( X17 != k1_xboole_0
        | k2_zfmisc_1(X17,X18) = k1_xboole_0 )
      & ( X18 != k1_xboole_0
        | k2_zfmisc_1(X17,X18) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_18,plain,(
    ! [X19,X20] :
      ( ( k4_xboole_0(X19,k1_tarski(X20)) != X19
        | ~ r2_hidden(X20,X19) )
      & ( r2_hidden(X20,X19)
        | k4_xboole_0(X19,k1_tarski(X20)) = X19 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | k4_xboole_0(k2_tarski(X1,X3),X2) = k2_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X36,X38,X39,X40] :
      ( ( r2_hidden(esk2_1(X36),X36)
        | X36 = k1_xboole_0 )
      & ( ~ r2_hidden(X38,X36)
        | esk2_1(X36) != k3_mcart_1(X38,X39,X40)
        | X36 = k1_xboole_0 )
      & ( ~ r2_hidden(X39,X36)
        | esk2_1(X36) != k3_mcart_1(X38,X39,X40)
        | X36 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k4_xboole_0(k1_enumset1(X1,X1,X3),X2) = k1_enumset1(X1,X1,X3)
    | r2_hidden(X3,X2)
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_20])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X2,X4) ),
    inference(rw,[status(thm)],[c_0_21,c_0_20])).

fof(c_0_27,plain,(
    ! [X30,X31,X32] :
      ( ( r2_hidden(k1_mcart_1(X30),X31)
        | ~ r2_hidden(X30,k2_zfmisc_1(X31,X32)) )
      & ( r2_hidden(k2_mcart_1(X30),X32)
        | ~ r2_hidden(X30,k2_zfmisc_1(X31,X32)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_28,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,k1_tarski(X2))
    | r2_hidden(X3,k1_tarski(X2))
    | ~ r2_hidden(X2,k1_enumset1(X1,X1,X3)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_26])])).

cnf(c_0_32,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k2_zfmisc_1(X1,X2) = X2
    | r2_hidden(esk2_1(X2),X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k1_tarski(X2))
    | r2_hidden(X2,k1_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k1_enumset1(X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_32,c_0_20])).

cnf(c_0_37,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | r2_hidden(k1_mcart_1(X2),X3)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(ef,[status(thm)],[c_0_35])).

cnf(c_0_39,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k1_enumset1(X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_40,plain,
    ( r2_hidden(esk2_1(k1_tarski(X1)),k1_tarski(X1))
    | r2_hidden(k1_mcart_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_41,negated_conjecture,(
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

cnf(c_0_42,plain,
    ( k1_mcart_1(X1) = X2
    | k1_mcart_1(X1) = X3
    | r2_hidden(esk2_1(k1_tarski(X1)),k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,X2)
    | k4_xboole_0(k2_tarski(X3,X1),X2) != k2_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_44,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & esk5_0 != k1_xboole_0
    & m1_subset_1(esk6_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0))
    & ( esk6_0 = k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)
      | esk6_0 = k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)
      | esk6_0 = k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_41])])])).

cnf(c_0_45,plain,
    ( k1_mcart_1(X1) = X2
    | r2_hidden(esk2_1(k1_tarski(X1)),k1_tarski(X1)) ),
    inference(ef,[status(thm)],[c_0_42])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k1_enumset1(X3,X3,X1),X2) != k1_enumset1(X3,X3,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_20]),c_0_20])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(X2,k1_tarski(X1)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_48,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,plain,
    ( X1 = X2
    | r2_hidden(esk2_1(k1_tarski(X3)),k1_tarski(X3)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_45])).

fof(c_0_50,plain,(
    ! [X45,X46,X47,X48] :
      ( ( k5_mcart_1(X45,X46,X47,X48) = k1_mcart_1(k1_mcart_1(X48))
        | ~ m1_subset_1(X48,k3_zfmisc_1(X45,X46,X47))
        | X45 = k1_xboole_0
        | X46 = k1_xboole_0
        | X47 = k1_xboole_0 )
      & ( k6_mcart_1(X45,X46,X47,X48) = k2_mcart_1(k1_mcart_1(X48))
        | ~ m1_subset_1(X48,k3_zfmisc_1(X45,X46,X47))
        | X45 = k1_xboole_0
        | X46 = k1_xboole_0
        | X47 = k1_xboole_0 )
      & ( k7_mcart_1(X45,X46,X47,X48) = k2_mcart_1(X48)
        | ~ m1_subset_1(X48,k3_zfmisc_1(X45,X46,X47))
        | X45 = k1_xboole_0
        | X46 = k1_xboole_0
        | X47 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

fof(c_0_51,plain,(
    ! [X27,X28,X29] : k3_zfmisc_1(X27,X28,X29) = k2_zfmisc_1(k2_zfmisc_1(X27,X28),X29) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X2,X3))
    | ~ r2_hidden(X3,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk2_1(k1_tarski(X1)),k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49])])).

cnf(c_0_54,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_55,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk6_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_57,plain,(
    ! [X33,X34,X35] :
      ( ( X33 != k1_mcart_1(X33)
        | X33 != k4_tarski(X34,X35) )
      & ( X33 != k2_mcart_1(X33)
        | X33 != k4_tarski(X34,X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).

fof(c_0_58,plain,(
    ! [X41,X42,X43,X44] :
      ( X41 = k1_xboole_0
      | X42 = k1_xboole_0
      | X43 = k1_xboole_0
      | ~ m1_subset_1(X44,k3_zfmisc_1(X41,X42,X43))
      | X44 = k3_mcart_1(k5_mcart_1(X41,X42,X43,X44),k6_mcart_1(X41,X42,X43,X44),k7_mcart_1(X41,X42,X43,X44)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).

fof(c_0_59,plain,(
    ! [X24,X25,X26] : k3_mcart_1(X24,X25,X26) = k4_tarski(k4_tarski(X24,X25),X26) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_60,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_61,plain,
    ( k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(X1,k1_enumset1(X2,X2,esk2_1(k1_tarski(X1)))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_63,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk6_0,k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)) ),
    inference(rw,[status(thm)],[c_0_56,c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_66,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_67,plain,
    ( X1 != k2_mcart_1(X1)
    | X1 != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_68,plain,(
    ! [X49,X50] :
      ( k1_mcart_1(k4_tarski(X49,X50)) = X49
      & k2_mcart_1(k4_tarski(X49,X50)) = X50 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_69,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_70,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_71,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_60,c_0_55])).

cnf(c_0_72,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_61,c_0_55])).

cnf(c_0_73,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk2_1(X2) != k3_mcart_1(X3,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_74,negated_conjecture,
    ( esk2_1(k1_tarski(X1)) = X1
    | X1 = X2 ),
    inference(spm,[status(thm)],[c_0_39,c_0_62])).

cnf(c_0_75,negated_conjecture,
    ( esk6_0 = k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)
    | esk6_0 = k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)
    | esk6_0 = k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_76,negated_conjecture,
    ( k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = k2_mcart_1(esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_48]),c_0_65]),c_0_66])).

cnf(c_0_77,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) != k4_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_78,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_79,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70]),c_0_55])).

cnf(c_0_80,negated_conjecture,
    ( k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = k1_mcart_1(k1_mcart_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_64]),c_0_48]),c_0_65]),c_0_66])).

cnf(c_0_81,negated_conjecture,
    ( k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = k2_mcart_1(k1_mcart_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_64]),c_0_48]),c_0_65]),c_0_66])).

cnf(c_0_82,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk2_1(X2) != k3_mcart_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_83,plain,
    ( X2 = k1_xboole_0
    | esk2_1(X2) != k4_tarski(k4_tarski(X3,X1),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_73,c_0_70])).

cnf(c_0_84,negated_conjecture,
    ( esk2_1(k1_tarski(X1)) = X1 ),
    inference(ef,[status(thm)],[c_0_74])).

cnf(c_0_85,negated_conjecture,
    ( k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = esk6_0
    | k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = esk6_0
    | k2_mcart_1(esk6_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_86,plain,
    ( k4_tarski(X1,X2) != X2 ),
    inference(rw,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_87,negated_conjecture,
    ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(esk6_0)),k2_mcart_1(k1_mcart_1(esk6_0))),k2_mcart_1(esk6_0)) = esk6_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_64]),c_0_80]),c_0_81]),c_0_76]),c_0_48]),c_0_65]),c_0_66])).

cnf(c_0_88,plain,
    ( X2 = k1_xboole_0
    | esk2_1(X2) != k4_tarski(k4_tarski(X1,X3),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_82,c_0_70])).

cnf(c_0_89,negated_conjecture,
    ( k1_tarski(k4_tarski(k4_tarski(X1,X2),X3)) = k1_xboole_0
    | ~ r2_hidden(X2,k1_tarski(k4_tarski(k4_tarski(X1,X2),X3))) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84])])).

cnf(c_0_90,negated_conjecture,
    ( k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = esk6_0
    | k1_mcart_1(k1_mcart_1(esk6_0)) = esk6_0
    | k2_mcart_1(esk6_0) = esk6_0 ),
    inference(rw,[status(thm)],[c_0_85,c_0_80])).

cnf(c_0_91,negated_conjecture,
    ( k2_mcart_1(esk6_0) != esk6_0 ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_92,negated_conjecture,
    ( k1_tarski(k4_tarski(k4_tarski(X1,X2),X3)) = k1_xboole_0
    | ~ r2_hidden(X1,k1_tarski(k4_tarski(k4_tarski(X1,X2),X3))) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_84])])).

cnf(c_0_93,negated_conjecture,
    ( k1_tarski(esk6_0) = k1_xboole_0
    | ~ r2_hidden(k2_mcart_1(k1_mcart_1(esk6_0)),k1_tarski(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_87])).

cnf(c_0_94,negated_conjecture,
    ( k1_mcart_1(k1_mcart_1(esk6_0)) = esk6_0
    | k2_mcart_1(k1_mcart_1(esk6_0)) = esk6_0 ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[c_0_90,c_0_91]),c_0_81])).

cnf(c_0_95,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_96,negated_conjecture,
    ( k1_tarski(esk6_0) = k1_xboole_0
    | ~ r2_hidden(k1_mcart_1(k1_mcart_1(esk6_0)),k1_tarski(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_87])).

cnf(c_0_97,negated_conjecture,
    ( k1_mcart_1(k1_mcart_1(esk6_0)) = esk6_0
    | k1_tarski(esk6_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_38])])).

cnf(c_0_98,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_99,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_95])).

cnf(c_0_100,negated_conjecture,
    ( k1_tarski(esk6_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_38])])).

cnf(c_0_101,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(esk6_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_100])).

cnf(c_0_103,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_104,plain,
    ( X1 != k1_mcart_1(X1)
    | X1 != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_105,negated_conjecture,
    ( X1 = k1_xboole_0
    | esk2_1(X1) != k4_tarski(esk6_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_87]),c_0_103])])).

cnf(c_0_106,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) != k4_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_104])).

cnf(c_0_107,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_108,negated_conjecture,
    ( k1_tarski(k4_tarski(esk6_0,X1)) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_84])])).

cnf(c_0_109,negated_conjecture,
    ( esk2_1(k1_xboole_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_84,c_0_100])).

cnf(c_0_110,plain,
    ( k4_tarski(X1,X2) != X1 ),
    inference(rw,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_111,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_108]),c_0_109]),c_0_110]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:08:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.71/0.91  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.71/0.91  # and selection function SelectNegativeLiterals.
% 0.71/0.91  #
% 0.71/0.91  # Preprocessing time       : 0.029 s
% 0.71/0.91  # Presaturation interreduction done
% 0.71/0.91  
% 0.71/0.91  # Proof found!
% 0.71/0.91  # SZS status Theorem
% 0.71/0.91  # SZS output start CNFRefutation
% 0.71/0.91  fof(t72_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)<=>(~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 0.71/0.91  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.71/0.91  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.71/0.91  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.71/0.91  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.71/0.91  fof(t29_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k3_mcart_1(X3,X4,X5))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 0.71/0.91  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.71/0.91  fof(t51_mcart_1, conjecture, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_mcart_1)).
% 0.71/0.91  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.71/0.91  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.71/0.91  fof(t20_mcart_1, axiom, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.71/0.91  fof(t48_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 0.71/0.91  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.71/0.91  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.71/0.91  fof(c_0_14, plain, ![X21, X22, X23]:(((~r2_hidden(X21,X23)|k4_xboole_0(k2_tarski(X21,X22),X23)!=k2_tarski(X21,X22))&(~r2_hidden(X22,X23)|k4_xboole_0(k2_tarski(X21,X22),X23)!=k2_tarski(X21,X22)))&(r2_hidden(X21,X23)|r2_hidden(X22,X23)|k4_xboole_0(k2_tarski(X21,X22),X23)=k2_tarski(X21,X22))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).
% 0.71/0.91  fof(c_0_15, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.71/0.91  fof(c_0_16, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X9,X8)|(X9=X6|X9=X7)|X8!=k2_tarski(X6,X7))&((X10!=X6|r2_hidden(X10,X8)|X8!=k2_tarski(X6,X7))&(X10!=X7|r2_hidden(X10,X8)|X8!=k2_tarski(X6,X7))))&(((esk1_3(X11,X12,X13)!=X11|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_tarski(X11,X12))&(esk1_3(X11,X12,X13)!=X12|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_tarski(X11,X12)))&(r2_hidden(esk1_3(X11,X12,X13),X13)|(esk1_3(X11,X12,X13)=X11|esk1_3(X11,X12,X13)=X12)|X13=k2_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.71/0.91  fof(c_0_17, plain, ![X17, X18]:((k2_zfmisc_1(X17,X18)!=k1_xboole_0|(X17=k1_xboole_0|X18=k1_xboole_0))&((X17!=k1_xboole_0|k2_zfmisc_1(X17,X18)=k1_xboole_0)&(X18!=k1_xboole_0|k2_zfmisc_1(X17,X18)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.71/0.91  fof(c_0_18, plain, ![X19, X20]:((k4_xboole_0(X19,k1_tarski(X20))!=X19|~r2_hidden(X20,X19))&(r2_hidden(X20,X19)|k4_xboole_0(X19,k1_tarski(X20))=X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.71/0.91  cnf(c_0_19, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|k4_xboole_0(k2_tarski(X1,X3),X2)=k2_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.71/0.91  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.71/0.91  cnf(c_0_21, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.71/0.91  cnf(c_0_22, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.71/0.91  fof(c_0_23, plain, ![X36, X38, X39, X40]:((r2_hidden(esk2_1(X36),X36)|X36=k1_xboole_0)&((~r2_hidden(X38,X36)|esk2_1(X36)!=k3_mcart_1(X38,X39,X40)|X36=k1_xboole_0)&(~r2_hidden(X39,X36)|esk2_1(X36)!=k3_mcart_1(X38,X39,X40)|X36=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).
% 0.71/0.91  cnf(c_0_24, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.71/0.91  cnf(c_0_25, plain, (k4_xboole_0(k1_enumset1(X1,X1,X3),X2)=k1_enumset1(X1,X1,X3)|r2_hidden(X3,X2)|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_20])).
% 0.71/0.91  cnf(c_0_26, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X2,X4)), inference(rw,[status(thm)],[c_0_21, c_0_20])).
% 0.71/0.91  fof(c_0_27, plain, ![X30, X31, X32]:((r2_hidden(k1_mcart_1(X30),X31)|~r2_hidden(X30,k2_zfmisc_1(X31,X32)))&(r2_hidden(k2_mcart_1(X30),X32)|~r2_hidden(X30,k2_zfmisc_1(X31,X32)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.71/0.91  cnf(c_0_28, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_22])).
% 0.71/0.91  cnf(c_0_29, plain, (r2_hidden(esk2_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.71/0.91  cnf(c_0_30, plain, (r2_hidden(X1,k1_tarski(X2))|r2_hidden(X3,k1_tarski(X2))|~r2_hidden(X2,k1_enumset1(X1,X1,X3))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.71/0.91  cnf(c_0_31, plain, (r2_hidden(X1,k1_enumset1(X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_26])])).
% 0.71/0.91  cnf(c_0_32, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.71/0.91  cnf(c_0_33, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.71/0.91  cnf(c_0_34, plain, (k2_zfmisc_1(X1,X2)=X2|r2_hidden(esk2_1(X2),X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.71/0.91  cnf(c_0_35, plain, (r2_hidden(X1,k1_tarski(X2))|r2_hidden(X2,k1_tarski(X2))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.71/0.91  cnf(c_0_36, plain, (X1=X4|X1=X3|X2!=k1_enumset1(X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_32, c_0_20])).
% 0.71/0.91  cnf(c_0_37, plain, (r2_hidden(esk2_1(X1),X1)|r2_hidden(k1_mcart_1(X2),X3)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.71/0.91  cnf(c_0_38, plain, (r2_hidden(X1,k1_tarski(X1))), inference(ef,[status(thm)],[c_0_35])).
% 0.71/0.91  cnf(c_0_39, plain, (X1=X2|X1=X3|~r2_hidden(X1,k1_enumset1(X3,X3,X2))), inference(er,[status(thm)],[c_0_36])).
% 0.71/0.91  cnf(c_0_40, plain, (r2_hidden(esk2_1(k1_tarski(X1)),k1_tarski(X1))|r2_hidden(k1_mcart_1(X1),X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.71/0.91  fof(c_0_41, negated_conjecture, ~(![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4))))))), inference(assume_negation,[status(cth)],[t51_mcart_1])).
% 0.71/0.91  cnf(c_0_42, plain, (k1_mcart_1(X1)=X2|k1_mcart_1(X1)=X3|r2_hidden(esk2_1(k1_tarski(X1)),k1_tarski(X1))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.71/0.91  cnf(c_0_43, plain, (~r2_hidden(X1,X2)|k4_xboole_0(k2_tarski(X3,X1),X2)!=k2_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.71/0.91  fof(c_0_44, negated_conjecture, (((esk3_0!=k1_xboole_0&esk4_0!=k1_xboole_0)&esk5_0!=k1_xboole_0)&(m1_subset_1(esk6_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0))&(esk6_0=k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)|esk6_0=k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)|esk6_0=k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_41])])])).
% 0.71/0.91  cnf(c_0_45, plain, (k1_mcart_1(X1)=X2|r2_hidden(esk2_1(k1_tarski(X1)),k1_tarski(X1))), inference(ef,[status(thm)],[c_0_42])).
% 0.71/0.91  cnf(c_0_46, plain, (k4_xboole_0(k1_enumset1(X3,X3,X1),X2)!=k1_enumset1(X3,X3,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_20]), c_0_20])).
% 0.71/0.91  cnf(c_0_47, plain, (r2_hidden(X1,X2)|k4_xboole_0(X2,k1_tarski(X1))=X2), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.71/0.91  cnf(c_0_48, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.71/0.91  cnf(c_0_49, plain, (X1=X2|r2_hidden(esk2_1(k1_tarski(X3)),k1_tarski(X3))), inference(spm,[status(thm)],[c_0_45, c_0_45])).
% 0.71/0.91  fof(c_0_50, plain, ![X45, X46, X47, X48]:(((k5_mcart_1(X45,X46,X47,X48)=k1_mcart_1(k1_mcart_1(X48))|~m1_subset_1(X48,k3_zfmisc_1(X45,X46,X47))|(X45=k1_xboole_0|X46=k1_xboole_0|X47=k1_xboole_0))&(k6_mcart_1(X45,X46,X47,X48)=k2_mcart_1(k1_mcart_1(X48))|~m1_subset_1(X48,k3_zfmisc_1(X45,X46,X47))|(X45=k1_xboole_0|X46=k1_xboole_0|X47=k1_xboole_0)))&(k7_mcart_1(X45,X46,X47,X48)=k2_mcart_1(X48)|~m1_subset_1(X48,k3_zfmisc_1(X45,X46,X47))|(X45=k1_xboole_0|X46=k1_xboole_0|X47=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.71/0.91  fof(c_0_51, plain, ![X27, X28, X29]:k3_zfmisc_1(X27,X28,X29)=k2_zfmisc_1(k2_zfmisc_1(X27,X28),X29), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.71/0.91  cnf(c_0_52, plain, (r2_hidden(X1,k1_enumset1(X2,X2,X3))|~r2_hidden(X3,k1_tarski(X1))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.71/0.91  cnf(c_0_53, negated_conjecture, (r2_hidden(esk2_1(k1_tarski(X1)),k1_tarski(X1))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49])])).
% 0.71/0.91  cnf(c_0_54, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.71/0.91  cnf(c_0_55, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.71/0.91  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk6_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.71/0.91  fof(c_0_57, plain, ![X33, X34, X35]:((X33!=k1_mcart_1(X33)|X33!=k4_tarski(X34,X35))&(X33!=k2_mcart_1(X33)|X33!=k4_tarski(X34,X35))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).
% 0.71/0.91  fof(c_0_58, plain, ![X41, X42, X43, X44]:(X41=k1_xboole_0|X42=k1_xboole_0|X43=k1_xboole_0|(~m1_subset_1(X44,k3_zfmisc_1(X41,X42,X43))|X44=k3_mcart_1(k5_mcart_1(X41,X42,X43,X44),k6_mcart_1(X41,X42,X43,X44),k7_mcart_1(X41,X42,X43,X44)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).
% 0.71/0.91  fof(c_0_59, plain, ![X24, X25, X26]:k3_mcart_1(X24,X25,X26)=k4_tarski(k4_tarski(X24,X25),X26), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.71/0.91  cnf(c_0_60, plain, (k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.71/0.91  cnf(c_0_61, plain, (k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.71/0.91  cnf(c_0_62, negated_conjecture, (r2_hidden(X1,k1_enumset1(X2,X2,esk2_1(k1_tarski(X1))))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.71/0.91  cnf(c_0_63, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_54, c_0_55])).
% 0.71/0.91  cnf(c_0_64, negated_conjecture, (m1_subset_1(esk6_0,k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0))), inference(rw,[status(thm)],[c_0_56, c_0_55])).
% 0.71/0.91  cnf(c_0_65, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.71/0.91  cnf(c_0_66, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.71/0.91  cnf(c_0_67, plain, (X1!=k2_mcart_1(X1)|X1!=k4_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.71/0.91  fof(c_0_68, plain, ![X49, X50]:(k1_mcart_1(k4_tarski(X49,X50))=X49&k2_mcart_1(k4_tarski(X49,X50))=X50), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.71/0.91  cnf(c_0_69, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.71/0.91  cnf(c_0_70, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.71/0.91  cnf(c_0_71, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_60, c_0_55])).
% 0.71/0.91  cnf(c_0_72, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_61, c_0_55])).
% 0.71/0.91  cnf(c_0_73, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk2_1(X2)!=k3_mcart_1(X3,X1,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.71/0.91  cnf(c_0_74, negated_conjecture, (esk2_1(k1_tarski(X1))=X1|X1=X2), inference(spm,[status(thm)],[c_0_39, c_0_62])).
% 0.71/0.91  cnf(c_0_75, negated_conjecture, (esk6_0=k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)|esk6_0=k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)|esk6_0=k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.71/0.91  cnf(c_0_76, negated_conjecture, (k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=k2_mcart_1(esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_48]), c_0_65]), c_0_66])).
% 0.71/0.91  cnf(c_0_77, plain, (k2_mcart_1(k4_tarski(X1,X2))!=k4_tarski(X1,X2)), inference(er,[status(thm)],[c_0_67])).
% 0.71/0.91  cnf(c_0_78, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.71/0.91  cnf(c_0_79, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X4=k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70]), c_0_55])).
% 0.71/0.91  cnf(c_0_80, negated_conjecture, (k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=k1_mcart_1(k1_mcart_1(esk6_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_64]), c_0_48]), c_0_65]), c_0_66])).
% 0.71/0.91  cnf(c_0_81, negated_conjecture, (k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=k2_mcart_1(k1_mcart_1(esk6_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_64]), c_0_48]), c_0_65]), c_0_66])).
% 0.71/0.91  cnf(c_0_82, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk2_1(X2)!=k3_mcart_1(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.71/0.91  cnf(c_0_83, plain, (X2=k1_xboole_0|esk2_1(X2)!=k4_tarski(k4_tarski(X3,X1),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_73, c_0_70])).
% 0.71/0.91  cnf(c_0_84, negated_conjecture, (esk2_1(k1_tarski(X1))=X1), inference(ef,[status(thm)],[c_0_74])).
% 0.71/0.91  cnf(c_0_85, negated_conjecture, (k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=esk6_0|k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=esk6_0|k2_mcart_1(esk6_0)=esk6_0), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.71/0.91  cnf(c_0_86, plain, (k4_tarski(X1,X2)!=X2), inference(rw,[status(thm)],[c_0_77, c_0_78])).
% 0.71/0.91  cnf(c_0_87, negated_conjecture, (k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(esk6_0)),k2_mcart_1(k1_mcart_1(esk6_0))),k2_mcart_1(esk6_0))=esk6_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_64]), c_0_80]), c_0_81]), c_0_76]), c_0_48]), c_0_65]), c_0_66])).
% 0.71/0.91  cnf(c_0_88, plain, (X2=k1_xboole_0|esk2_1(X2)!=k4_tarski(k4_tarski(X1,X3),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_82, c_0_70])).
% 0.71/0.91  cnf(c_0_89, negated_conjecture, (k1_tarski(k4_tarski(k4_tarski(X1,X2),X3))=k1_xboole_0|~r2_hidden(X2,k1_tarski(k4_tarski(k4_tarski(X1,X2),X3)))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84])])).
% 0.71/0.91  cnf(c_0_90, negated_conjecture, (k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=esk6_0|k1_mcart_1(k1_mcart_1(esk6_0))=esk6_0|k2_mcart_1(esk6_0)=esk6_0), inference(rw,[status(thm)],[c_0_85, c_0_80])).
% 0.71/0.91  cnf(c_0_91, negated_conjecture, (k2_mcart_1(esk6_0)!=esk6_0), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.71/0.91  cnf(c_0_92, negated_conjecture, (k1_tarski(k4_tarski(k4_tarski(X1,X2),X3))=k1_xboole_0|~r2_hidden(X1,k1_tarski(k4_tarski(k4_tarski(X1,X2),X3)))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_84])])).
% 0.71/0.91  cnf(c_0_93, negated_conjecture, (k1_tarski(esk6_0)=k1_xboole_0|~r2_hidden(k2_mcart_1(k1_mcart_1(esk6_0)),k1_tarski(esk6_0))), inference(spm,[status(thm)],[c_0_89, c_0_87])).
% 0.71/0.91  cnf(c_0_94, negated_conjecture, (k1_mcart_1(k1_mcart_1(esk6_0))=esk6_0|k2_mcart_1(k1_mcart_1(esk6_0))=esk6_0), inference(rw,[status(thm)],[inference(sr,[status(thm)],[c_0_90, c_0_91]), c_0_81])).
% 0.71/0.91  cnf(c_0_95, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.71/0.91  cnf(c_0_96, negated_conjecture, (k1_tarski(esk6_0)=k1_xboole_0|~r2_hidden(k1_mcart_1(k1_mcart_1(esk6_0)),k1_tarski(esk6_0))), inference(spm,[status(thm)],[c_0_92, c_0_87])).
% 0.71/0.91  cnf(c_0_97, negated_conjecture, (k1_mcart_1(k1_mcart_1(esk6_0))=esk6_0|k1_tarski(esk6_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_38])])).
% 0.71/0.91  cnf(c_0_98, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.71/0.91  cnf(c_0_99, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_95])).
% 0.71/0.91  cnf(c_0_100, negated_conjecture, (k1_tarski(esk6_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_38])])).
% 0.71/0.91  cnf(c_0_101, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 0.71/0.91  cnf(c_0_102, negated_conjecture, (r2_hidden(esk6_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_38, c_0_100])).
% 0.71/0.91  cnf(c_0_103, negated_conjecture, (r2_hidden(k2_mcart_1(esk6_0),X1)), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 0.71/0.91  cnf(c_0_104, plain, (X1!=k1_mcart_1(X1)|X1!=k4_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.71/0.91  cnf(c_0_105, negated_conjecture, (X1=k1_xboole_0|esk2_1(X1)!=k4_tarski(esk6_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_87]), c_0_103])])).
% 0.71/0.91  cnf(c_0_106, plain, (k1_mcart_1(k4_tarski(X1,X2))!=k4_tarski(X1,X2)), inference(er,[status(thm)],[c_0_104])).
% 0.71/0.91  cnf(c_0_107, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.71/0.91  cnf(c_0_108, negated_conjecture, (k1_tarski(k4_tarski(esk6_0,X1))=k1_xboole_0), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_84])])).
% 0.71/0.91  cnf(c_0_109, negated_conjecture, (esk2_1(k1_xboole_0)=esk6_0), inference(spm,[status(thm)],[c_0_84, c_0_100])).
% 0.71/0.91  cnf(c_0_110, plain, (k4_tarski(X1,X2)!=X1), inference(rw,[status(thm)],[c_0_106, c_0_107])).
% 0.71/0.91  cnf(c_0_111, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_108]), c_0_109]), c_0_110]), ['proof']).
% 0.71/0.91  # SZS output end CNFRefutation
% 0.71/0.91  # Proof object total steps             : 112
% 0.71/0.91  # Proof object clause steps            : 83
% 0.71/0.91  # Proof object formula steps           : 29
% 0.71/0.91  # Proof object conjectures             : 33
% 0.71/0.91  # Proof object clause conjectures      : 30
% 0.71/0.91  # Proof object formula conjectures     : 3
% 0.71/0.91  # Proof object initial clauses used    : 29
% 0.71/0.91  # Proof object initial formulas used   : 14
% 0.71/0.91  # Proof object generating inferences   : 33
% 0.71/0.91  # Proof object simplifying inferences  : 53
% 0.71/0.91  # Training examples: 0 positive, 0 negative
% 0.71/0.91  # Parsed axioms                        : 14
% 0.71/0.91  # Removed by relevancy pruning/SinE    : 0
% 0.71/0.91  # Initial clauses                      : 35
% 0.71/0.91  # Removed in clause preprocessing      : 3
% 0.71/0.91  # Initial clauses in saturation        : 32
% 0.71/0.91  # Processed clauses                    : 2022
% 0.71/0.91  # ...of these trivial                  : 137
% 0.71/0.91  # ...subsumed                          : 1234
% 0.71/0.91  # ...remaining for further processing  : 651
% 0.71/0.91  # Other redundant clauses eliminated   : 5862
% 0.71/0.91  # Clauses deleted for lack of memory   : 0
% 0.71/0.91  # Backward-subsumed                    : 48
% 0.71/0.91  # Backward-rewritten                   : 34
% 0.71/0.91  # Generated clauses                    : 77012
% 0.71/0.91  # ...of the previous two non-trivial   : 61103
% 0.71/0.91  # Contextual simplify-reflections      : 11
% 0.71/0.91  # Paramodulations                      : 71035
% 0.71/0.91  # Factorizations                       : 112
% 0.71/0.91  # Equation resolutions                 : 5864
% 0.71/0.91  # Propositional unsat checks           : 0
% 0.71/0.91  #    Propositional check models        : 0
% 0.71/0.91  #    Propositional check unsatisfiable : 0
% 0.71/0.91  #    Propositional clauses             : 0
% 0.71/0.91  #    Propositional clauses after purity: 0
% 0.71/0.91  #    Propositional unsat core size     : 0
% 0.71/0.91  #    Propositional preprocessing time  : 0.000
% 0.71/0.91  #    Propositional encoding time       : 0.000
% 0.71/0.91  #    Propositional solver time         : 0.000
% 0.71/0.91  #    Success case prop preproc time    : 0.000
% 0.71/0.91  #    Success case prop encoding time   : 0.000
% 0.71/0.91  #    Success case prop solver time     : 0.000
% 0.71/0.91  # Current number of processed clauses  : 527
% 0.71/0.91  #    Positive orientable unit clauses  : 55
% 0.71/0.91  #    Positive unorientable unit clauses: 0
% 0.71/0.91  #    Negative unit clauses             : 7
% 0.71/0.91  #    Non-unit-clauses                  : 465
% 0.71/0.91  # Current number of unprocessed clauses: 57741
% 0.71/0.91  # ...number of literals in the above   : 258260
% 0.71/0.91  # Current number of archived formulas  : 0
% 0.71/0.91  # Current number of archived clauses   : 120
% 0.71/0.91  # Clause-clause subsumption calls (NU) : 59534
% 0.71/0.91  # Rec. Clause-clause subsumption calls : 24001
% 0.71/0.91  # Non-unit clause-clause subsumptions  : 1271
% 0.71/0.91  # Unit Clause-clause subsumption calls : 2251
% 0.71/0.91  # Rewrite failures with RHS unbound    : 0
% 0.71/0.91  # BW rewrite match attempts            : 59
% 0.71/0.91  # BW rewrite match successes           : 24
% 0.71/0.91  # Condensation attempts                : 0
% 0.71/0.91  # Condensation successes               : 0
% 0.71/0.91  # Termbank termtop insertions          : 1422613
% 0.71/0.92  
% 0.71/0.92  # -------------------------------------------------
% 0.71/0.92  # User time                : 0.543 s
% 0.71/0.92  # System time              : 0.022 s
% 0.71/0.92  # Total time               : 0.566 s
% 0.71/0.92  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
