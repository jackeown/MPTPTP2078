%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:56 EST 2020

% Result     : Theorem 0.41s
% Output     : CNFRefutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 311 expanded)
%              Number of clauses        :   50 ( 140 expanded)
%              Number of leaves         :   11 (  75 expanded)
%              Depth                    :   13
%              Number of atoms          :  194 (1101 expanded)
%              Number of equality atoms :  146 ( 871 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

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

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

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

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(t20_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(c_0_11,negated_conjecture,(
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

fof(c_0_12,plain,(
    ! [X17,X18] :
      ( ( k2_zfmisc_1(X17,X18) != k1_xboole_0
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0 )
      & ( X17 != k1_xboole_0
        | k2_zfmisc_1(X17,X18) = k1_xboole_0 )
      & ( X18 != k1_xboole_0
        | k2_zfmisc_1(X17,X18) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_13,plain,(
    ! [X35,X36,X37,X38] :
      ( X35 = k1_xboole_0
      | X36 = k1_xboole_0
      | X37 = k1_xboole_0
      | ~ m1_subset_1(X38,k3_zfmisc_1(X35,X36,X37))
      | X38 = k3_mcart_1(k5_mcart_1(X35,X36,X37,X38),k6_mcart_1(X35,X36,X37,X38),k7_mcart_1(X35,X36,X37,X38)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).

fof(c_0_14,plain,(
    ! [X21,X22,X23] : k3_mcart_1(X21,X22,X23) = k4_tarski(k4_tarski(X21,X22),X23) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_15,plain,(
    ! [X24,X25,X26] : k3_zfmisc_1(X24,X25,X26) = k2_zfmisc_1(k2_zfmisc_1(X24,X25),X26) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_16,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & esk5_0 != k1_xboole_0
    & m1_subset_1(esk6_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0))
    & ( esk6_0 = k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)
      | esk6_0 = k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)
      | esk6_0 = k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_17,plain,(
    ! [X19,X20] : ~ r2_hidden(X19,k2_zfmisc_1(X19,X20)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_18,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,plain,(
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

fof(c_0_20,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk6_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_18])).

fof(c_0_27,plain,(
    ! [X30,X32,X33,X34] :
      ( ( r2_hidden(esk2_1(X30),X30)
        | X30 = k1_xboole_0 )
      & ( ~ r2_hidden(X32,X30)
        | esk2_1(X30) != k3_mcart_1(X32,X33,X34)
        | X30 = k1_xboole_0 )
      & ( ~ r2_hidden(X33,X30)
        | esk2_1(X30) != k3_mcart_1(X32,X33,X34)
        | X30 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_30,plain,(
    ! [X39,X40] :
      ( k1_mcart_1(k4_tarski(X39,X40)) = X39
      & k2_mcart_1(k4_tarski(X39,X40)) = X40 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_31,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk6_0,k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_35,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_38,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X4,X2) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_40,plain,(
    ! [X27,X28,X29] :
      ( ( X27 != k1_mcart_1(X27)
        | X27 != k4_tarski(X28,X29) )
      & ( X27 != k2_mcart_1(X27)
        | X27 != k4_tarski(X28,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).

cnf(c_0_41,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( k4_tarski(k4_tarski(k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)),k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)) = esk6_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_43,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k1_enumset1(X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_36,c_0_29])).

cnf(c_0_44,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_39])])).

cnf(c_0_46,plain,
    ( X1 != k2_mcart_1(X1)
    | X1 != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk2_1(X2) != k3_mcart_1(X3,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_48,negated_conjecture,
    ( k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = k2_mcart_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k1_enumset1(X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_50,plain,
    ( r2_hidden(esk2_1(k1_enumset1(X1,X1,X2)),k1_enumset1(X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) != k4_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_52,plain,
    ( X2 = k1_xboole_0
    | esk2_1(X2) != k4_tarski(k4_tarski(X3,X1),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_47,c_0_22])).

cnf(c_0_53,negated_conjecture,
    ( k4_tarski(k4_tarski(k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)),k2_mcart_1(esk6_0)) = esk6_0 ),
    inference(rw,[status(thm)],[c_0_42,c_0_48])).

cnf(c_0_54,plain,
    ( esk2_1(k1_enumset1(X1,X1,X2)) = X2
    | esk2_1(k1_enumset1(X1,X1,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,plain,
    ( k4_tarski(X1,X2) != X2 ),
    inference(rw,[status(thm)],[c_0_51,c_0_41])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_57,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk2_1(X2) != k3_mcart_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_58,negated_conjecture,
    ( X1 = k1_xboole_0
    | esk2_1(X1) != esk6_0
    | ~ r2_hidden(k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,plain,
    ( esk2_1(k1_enumset1(X1,X1,X1)) = X1 ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_54])])).

cnf(c_0_60,negated_conjecture,
    ( esk6_0 = k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)
    | esk6_0 = k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)
    | esk6_0 = k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_61,negated_conjecture,
    ( k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) != esk6_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_42])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X2,X4) ),
    inference(rw,[status(thm)],[c_0_56,c_0_29])).

cnf(c_0_63,plain,
    ( X2 = k1_xboole_0
    | esk2_1(X2) != k4_tarski(k4_tarski(X1,X3),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_57,c_0_22])).

cnf(c_0_64,negated_conjecture,
    ( k1_enumset1(esk6_0,esk6_0,esk6_0) = k1_xboole_0
    | ~ r2_hidden(k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),k1_enumset1(esk6_0,esk6_0,esk6_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59])])).

cnf(c_0_65,negated_conjecture,
    ( k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = esk6_0
    | k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = esk6_0 ),
    inference(sr,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_62])])).

cnf(c_0_67,negated_conjecture,
    ( X1 = k1_xboole_0
    | esk2_1(X1) != esk6_0
    | ~ r2_hidden(k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_53])).

cnf(c_0_68,negated_conjecture,
    ( k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = esk6_0
    | k1_enumset1(esk6_0,esk6_0,esk6_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])])).

cnf(c_0_69,negated_conjecture,
    ( k1_enumset1(esk6_0,esk6_0,esk6_0) = k1_xboole_0
    | ~ r2_hidden(k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),k1_enumset1(esk6_0,esk6_0,esk6_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_59])])).

cnf(c_0_70,negated_conjecture,
    ( k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = esk6_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_68]),c_0_37])).

cnf(c_0_71,negated_conjecture,
    ( k1_enumset1(esk6_0,esk6_0,esk6_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70]),c_0_66])])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_71]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:46:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.41/0.60  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.41/0.60  # and selection function SelectNegativeLiterals.
% 0.41/0.60  #
% 0.41/0.60  # Preprocessing time       : 0.028 s
% 0.41/0.60  # Presaturation interreduction done
% 0.41/0.60  
% 0.41/0.60  # Proof found!
% 0.41/0.60  # SZS status Theorem
% 0.41/0.60  # SZS output start CNFRefutation
% 0.41/0.60  fof(t51_mcart_1, conjecture, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_mcart_1)).
% 0.41/0.60  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.41/0.60  fof(t48_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 0.41/0.60  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.41/0.60  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.41/0.60  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.41/0.60  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.41/0.60  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.41/0.60  fof(t29_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k3_mcart_1(X3,X4,X5))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 0.41/0.60  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.41/0.60  fof(t20_mcart_1, axiom, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.41/0.60  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4))))))), inference(assume_negation,[status(cth)],[t51_mcart_1])).
% 0.41/0.60  fof(c_0_12, plain, ![X17, X18]:((k2_zfmisc_1(X17,X18)!=k1_xboole_0|(X17=k1_xboole_0|X18=k1_xboole_0))&((X17!=k1_xboole_0|k2_zfmisc_1(X17,X18)=k1_xboole_0)&(X18!=k1_xboole_0|k2_zfmisc_1(X17,X18)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.41/0.60  fof(c_0_13, plain, ![X35, X36, X37, X38]:(X35=k1_xboole_0|X36=k1_xboole_0|X37=k1_xboole_0|(~m1_subset_1(X38,k3_zfmisc_1(X35,X36,X37))|X38=k3_mcart_1(k5_mcart_1(X35,X36,X37,X38),k6_mcart_1(X35,X36,X37,X38),k7_mcart_1(X35,X36,X37,X38)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).
% 0.41/0.60  fof(c_0_14, plain, ![X21, X22, X23]:k3_mcart_1(X21,X22,X23)=k4_tarski(k4_tarski(X21,X22),X23), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.41/0.60  fof(c_0_15, plain, ![X24, X25, X26]:k3_zfmisc_1(X24,X25,X26)=k2_zfmisc_1(k2_zfmisc_1(X24,X25),X26), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.41/0.60  fof(c_0_16, negated_conjecture, (((esk3_0!=k1_xboole_0&esk4_0!=k1_xboole_0)&esk5_0!=k1_xboole_0)&(m1_subset_1(esk6_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0))&(esk6_0=k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)|esk6_0=k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)|esk6_0=k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.41/0.60  fof(c_0_17, plain, ![X19, X20]:~r2_hidden(X19,k2_zfmisc_1(X19,X20)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.41/0.60  cnf(c_0_18, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.41/0.60  fof(c_0_19, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X9,X8)|(X9=X6|X9=X7)|X8!=k2_tarski(X6,X7))&((X10!=X6|r2_hidden(X10,X8)|X8!=k2_tarski(X6,X7))&(X10!=X7|r2_hidden(X10,X8)|X8!=k2_tarski(X6,X7))))&(((esk1_3(X11,X12,X13)!=X11|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_tarski(X11,X12))&(esk1_3(X11,X12,X13)!=X12|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_tarski(X11,X12)))&(r2_hidden(esk1_3(X11,X12,X13),X13)|(esk1_3(X11,X12,X13)=X11|esk1_3(X11,X12,X13)=X12)|X13=k2_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.41/0.60  fof(c_0_20, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.41/0.60  cnf(c_0_21, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.41/0.60  cnf(c_0_22, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.41/0.60  cnf(c_0_23, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.41/0.60  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk6_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.41/0.60  cnf(c_0_25, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.41/0.60  cnf(c_0_26, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_18])).
% 0.41/0.61  fof(c_0_27, plain, ![X30, X32, X33, X34]:((r2_hidden(esk2_1(X30),X30)|X30=k1_xboole_0)&((~r2_hidden(X32,X30)|esk2_1(X30)!=k3_mcart_1(X32,X33,X34)|X30=k1_xboole_0)&(~r2_hidden(X33,X30)|esk2_1(X30)!=k3_mcart_1(X32,X33,X34)|X30=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).
% 0.41/0.61  cnf(c_0_28, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.41/0.61  cnf(c_0_29, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.41/0.61  fof(c_0_30, plain, ![X39, X40]:(k1_mcart_1(k4_tarski(X39,X40))=X39&k2_mcart_1(k4_tarski(X39,X40))=X40), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.41/0.61  cnf(c_0_31, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X4=k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.41/0.61  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk6_0,k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0))), inference(rw,[status(thm)],[c_0_24, c_0_23])).
% 0.41/0.61  cnf(c_0_33, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.41/0.61  cnf(c_0_34, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.41/0.61  cnf(c_0_35, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.41/0.61  cnf(c_0_36, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.41/0.61  cnf(c_0_37, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.41/0.61  cnf(c_0_38, plain, (r2_hidden(esk2_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.41/0.61  cnf(c_0_39, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X4,X2)), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.41/0.61  fof(c_0_40, plain, ![X27, X28, X29]:((X27!=k1_mcart_1(X27)|X27!=k4_tarski(X28,X29))&(X27!=k2_mcart_1(X27)|X27!=k4_tarski(X28,X29))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).
% 0.41/0.61  cnf(c_0_41, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.41/0.61  cnf(c_0_42, negated_conjecture, (k4_tarski(k4_tarski(k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)),k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0))=esk6_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.41/0.61  cnf(c_0_43, plain, (X1=X4|X1=X3|X2!=k1_enumset1(X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_36, c_0_29])).
% 0.41/0.61  cnf(c_0_44, plain, (r2_hidden(esk2_1(X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.41/0.61  cnf(c_0_45, plain, (r2_hidden(X1,k1_enumset1(X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_39])])).
% 0.41/0.61  cnf(c_0_46, plain, (X1!=k2_mcart_1(X1)|X1!=k4_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.41/0.61  cnf(c_0_47, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk2_1(X2)!=k3_mcart_1(X3,X1,X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.41/0.61  cnf(c_0_48, negated_conjecture, (k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=k2_mcart_1(esk6_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.41/0.61  cnf(c_0_49, plain, (X1=X2|X1=X3|~r2_hidden(X1,k1_enumset1(X3,X3,X2))), inference(er,[status(thm)],[c_0_43])).
% 0.41/0.61  cnf(c_0_50, plain, (r2_hidden(esk2_1(k1_enumset1(X1,X1,X2)),k1_enumset1(X1,X1,X2))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.41/0.61  cnf(c_0_51, plain, (k2_mcart_1(k4_tarski(X1,X2))!=k4_tarski(X1,X2)), inference(er,[status(thm)],[c_0_46])).
% 0.41/0.61  cnf(c_0_52, plain, (X2=k1_xboole_0|esk2_1(X2)!=k4_tarski(k4_tarski(X3,X1),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_47, c_0_22])).
% 0.41/0.61  cnf(c_0_53, negated_conjecture, (k4_tarski(k4_tarski(k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)),k2_mcart_1(esk6_0))=esk6_0), inference(rw,[status(thm)],[c_0_42, c_0_48])).
% 0.41/0.61  cnf(c_0_54, plain, (esk2_1(k1_enumset1(X1,X1,X2))=X2|esk2_1(k1_enumset1(X1,X1,X2))=X1), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.41/0.61  cnf(c_0_55, plain, (k4_tarski(X1,X2)!=X2), inference(rw,[status(thm)],[c_0_51, c_0_41])).
% 0.41/0.61  cnf(c_0_56, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.41/0.61  cnf(c_0_57, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk2_1(X2)!=k3_mcart_1(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.41/0.61  cnf(c_0_58, negated_conjecture, (X1=k1_xboole_0|esk2_1(X1)!=esk6_0|~r2_hidden(k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.41/0.61  cnf(c_0_59, plain, (esk2_1(k1_enumset1(X1,X1,X1))=X1), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_54])])).
% 0.41/0.61  cnf(c_0_60, negated_conjecture, (esk6_0=k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)|esk6_0=k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)|esk6_0=k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.41/0.61  cnf(c_0_61, negated_conjecture, (k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)!=esk6_0), inference(spm,[status(thm)],[c_0_55, c_0_42])).
% 0.41/0.61  cnf(c_0_62, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X2,X4)), inference(rw,[status(thm)],[c_0_56, c_0_29])).
% 0.41/0.61  cnf(c_0_63, plain, (X2=k1_xboole_0|esk2_1(X2)!=k4_tarski(k4_tarski(X1,X3),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_57, c_0_22])).
% 0.41/0.61  cnf(c_0_64, negated_conjecture, (k1_enumset1(esk6_0,esk6_0,esk6_0)=k1_xboole_0|~r2_hidden(k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),k1_enumset1(esk6_0,esk6_0,esk6_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59])])).
% 0.41/0.61  cnf(c_0_65, negated_conjecture, (k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=esk6_0|k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=esk6_0), inference(sr,[status(thm)],[c_0_60, c_0_61])).
% 0.41/0.61  cnf(c_0_66, plain, (r2_hidden(X1,k1_enumset1(X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_62])])).
% 0.41/0.61  cnf(c_0_67, negated_conjecture, (X1=k1_xboole_0|esk2_1(X1)!=esk6_0|~r2_hidden(k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_63, c_0_53])).
% 0.41/0.61  cnf(c_0_68, negated_conjecture, (k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=esk6_0|k1_enumset1(esk6_0,esk6_0,esk6_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])])).
% 0.41/0.61  cnf(c_0_69, negated_conjecture, (k1_enumset1(esk6_0,esk6_0,esk6_0)=k1_xboole_0|~r2_hidden(k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),k1_enumset1(esk6_0,esk6_0,esk6_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_59])])).
% 0.41/0.61  cnf(c_0_70, negated_conjecture, (k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=esk6_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_68]), c_0_37])).
% 0.41/0.61  cnf(c_0_71, negated_conjecture, (k1_enumset1(esk6_0,esk6_0,esk6_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70]), c_0_66])])).
% 0.41/0.61  cnf(c_0_72, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_71]), c_0_37]), ['proof']).
% 0.41/0.61  # SZS output end CNFRefutation
% 0.41/0.61  # Proof object total steps             : 73
% 0.41/0.61  # Proof object clause steps            : 50
% 0.41/0.61  # Proof object formula steps           : 23
% 0.41/0.61  # Proof object conjectures             : 22
% 0.41/0.61  # Proof object clause conjectures      : 19
% 0.41/0.61  # Proof object formula conjectures     : 3
% 0.41/0.61  # Proof object initial clauses used    : 19
% 0.41/0.61  # Proof object initial formulas used   : 11
% 0.41/0.61  # Proof object generating inferences   : 15
% 0.41/0.61  # Proof object simplifying inferences  : 31
% 0.41/0.61  # Training examples: 0 positive, 0 negative
% 0.41/0.61  # Parsed axioms                        : 11
% 0.41/0.61  # Removed by relevancy pruning/SinE    : 0
% 0.41/0.61  # Initial clauses                      : 26
% 0.41/0.61  # Removed in clause preprocessing      : 3
% 0.41/0.61  # Initial clauses in saturation        : 23
% 0.41/0.61  # Processed clauses                    : 1599
% 0.41/0.61  # ...of these trivial                  : 82
% 0.41/0.61  # ...subsumed                          : 1148
% 0.41/0.61  # ...remaining for further processing  : 369
% 0.41/0.61  # Other redundant clauses eliminated   : 1310
% 0.41/0.61  # Clauses deleted for lack of memory   : 0
% 0.41/0.61  # Backward-subsumed                    : 2
% 0.41/0.61  # Backward-rewritten                   : 41
% 0.41/0.61  # Generated clauses                    : 22138
% 0.41/0.61  # ...of the previous two non-trivial   : 16962
% 0.41/0.61  # Contextual simplify-reflections      : 1
% 0.41/0.61  # Paramodulations                      : 20709
% 0.41/0.61  # Factorizations                       : 120
% 0.41/0.61  # Equation resolutions                 : 1310
% 0.41/0.61  # Propositional unsat checks           : 0
% 0.41/0.61  #    Propositional check models        : 0
% 0.41/0.61  #    Propositional check unsatisfiable : 0
% 0.41/0.61  #    Propositional clauses             : 0
% 0.41/0.61  #    Propositional clauses after purity: 0
% 0.41/0.61  #    Propositional unsat core size     : 0
% 0.41/0.61  #    Propositional preprocessing time  : 0.000
% 0.41/0.61  #    Propositional encoding time       : 0.000
% 0.41/0.61  #    Propositional solver time         : 0.000
% 0.41/0.61  #    Success case prop preproc time    : 0.000
% 0.41/0.61  #    Success case prop encoding time   : 0.000
% 0.41/0.61  #    Success case prop solver time     : 0.000
% 0.41/0.61  # Current number of processed clauses  : 295
% 0.41/0.61  #    Positive orientable unit clauses  : 29
% 0.41/0.61  #    Positive unorientable unit clauses: 0
% 0.41/0.61  #    Negative unit clauses             : 10
% 0.41/0.61  #    Non-unit-clauses                  : 256
% 0.41/0.61  # Current number of unprocessed clauses: 15317
% 0.41/0.61  # ...number of literals in the above   : 78610
% 0.41/0.61  # Current number of archived formulas  : 0
% 0.41/0.61  # Current number of archived clauses   : 70
% 0.41/0.61  # Clause-clause subsumption calls (NU) : 12993
% 0.41/0.61  # Rec. Clause-clause subsumption calls : 10165
% 0.41/0.61  # Non-unit clause-clause subsumptions  : 1118
% 0.41/0.61  # Unit Clause-clause subsumption calls : 204
% 0.41/0.61  # Rewrite failures with RHS unbound    : 0
% 0.41/0.61  # BW rewrite match attempts            : 41
% 0.41/0.61  # BW rewrite match successes           : 18
% 0.41/0.61  # Condensation attempts                : 0
% 0.41/0.61  # Condensation successes               : 0
% 0.41/0.61  # Termbank termtop insertions          : 403108
% 0.41/0.61  
% 0.41/0.61  # -------------------------------------------------
% 0.41/0.61  # User time                : 0.253 s
% 0.41/0.61  # System time              : 0.019 s
% 0.41/0.61  # Total time               : 0.273 s
% 0.41/0.61  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
