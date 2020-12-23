%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:55 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 497 expanded)
%              Number of clauses        :   50 ( 244 expanded)
%              Number of leaves         :    9 ( 120 expanded)
%              Depth                    :   14
%              Number of atoms          :  208 (2006 expanded)
%              Number of equality atoms :  136 (1195 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

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

fof(t9_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(t72_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    <=> ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

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

fof(c_0_9,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k4_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_10,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21] :
      ( ( ~ r2_hidden(X17,X16)
        | X17 = X14
        | X17 = X15
        | X16 != k2_tarski(X14,X15) )
      & ( X18 != X14
        | r2_hidden(X18,X16)
        | X16 != k2_tarski(X14,X15) )
      & ( X18 != X15
        | r2_hidden(X18,X16)
        | X16 != k2_tarski(X14,X15) )
      & ( esk2_3(X19,X20,X21) != X19
        | ~ r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k2_tarski(X19,X20) )
      & ( esk2_3(X19,X20,X21) != X20
        | ~ r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k2_tarski(X19,X20) )
      & ( r2_hidden(esk2_3(X19,X20,X21),X21)
        | esk2_3(X19,X20,X21) = X19
        | esk2_3(X19,X20,X21) = X20
        | X21 = k2_tarski(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_11,plain,(
    ! [X23,X24] : k1_enumset1(X23,X23,X24) = k2_tarski(X23,X24) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X38,X40,X41] :
      ( ( r2_hidden(esk3_1(X38),X38)
        | X38 = k1_xboole_0 )
      & ( ~ r2_hidden(X40,X38)
        | esk3_1(X38) != k4_tarski(X40,X41)
        | X38 = k1_xboole_0 )
      & ( ~ r2_hidden(X41,X38)
        | esk3_1(X38) != k4_tarski(X40,X41)
        | X38 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X25,X26,X27] :
      ( ( ~ r2_hidden(X25,X27)
        | k4_xboole_0(k2_tarski(X25,X26),X27) != k2_tarski(X25,X26) )
      & ( ~ r2_hidden(X26,X27)
        | k4_xboole_0(k2_tarski(X25,X26),X27) != k2_tarski(X25,X26) )
      & ( r2_hidden(X25,X27)
        | r2_hidden(X26,X27)
        | k4_xboole_0(k2_tarski(X25,X26),X27) = k2_tarski(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X4,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,X2)
    | k4_xboole_0(k2_tarski(X3,X1),X2) != k2_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r2_hidden(esk3_1(k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk3_1(k4_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X3,X1) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_28,negated_conjecture,(
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

cnf(c_0_29,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k1_enumset1(X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_16])).

cnf(c_0_30,plain,
    ( k4_xboole_0(k1_enumset1(X3,X3,X1),X2) != k1_enumset1(X3,X3,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_16]),c_0_16])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X2,X1)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X2,X4) ),
    inference(rw,[status(thm)],[c_0_27,c_0_16])).

fof(c_0_34,plain,(
    ! [X34,X35,X36,X37] :
      ( X34 = k1_xboole_0
      | X35 = k1_xboole_0
      | X36 = k1_xboole_0
      | ~ m1_subset_1(X37,k3_zfmisc_1(X34,X35,X36))
      | X37 = k3_mcart_1(k5_mcart_1(X34,X35,X36,X37),k6_mcart_1(X34,X35,X36,X37),k7_mcart_1(X34,X35,X36,X37)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).

fof(c_0_35,plain,(
    ! [X28,X29,X30] : k3_mcart_1(X28,X29,X30) = k4_tarski(k4_tarski(X28,X29),X30) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_36,plain,(
    ! [X31,X32,X33] : k3_zfmisc_1(X31,X32,X33) = k2_zfmisc_1(k2_zfmisc_1(X31,X32),X33) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_37,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    & esk5_0 != k1_xboole_0
    & esk6_0 != k1_xboole_0
    & m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
    & ( esk7_0 = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
      | esk7_0 = k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
      | esk7_0 = k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).

cnf(c_0_38,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k1_enumset1(X2,X2,X3)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k1_enumset1(X1,X1,X2) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_enumset1(X1,X1,X3) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk3_1(X2) != k4_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_46,plain,
    ( esk3_1(k1_enumset1(X1,X1,X2)) = X2
    | esk3_1(k1_enumset1(X1,X1,X2)) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_19]),c_0_39])).

cnf(c_0_47,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk3_1(X2) != k4_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X1,X2)) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( esk7_0 = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
    | esk7_0 = k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
    | esk7_0 = k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk7_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_53,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_54,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_55,plain,
    ( X1 = k1_xboole_0
    | k4_tarski(X2,esk3_1(X1)) != esk3_1(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_19])).

cnf(c_0_56,plain,
    ( esk3_1(k1_enumset1(X1,X1,X1)) = X1 ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_46])])).

cnf(c_0_57,plain,
    ( esk3_1(k1_enumset1(X1,X1,X2)) != k4_tarski(X1,X3) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_39])).

cnf(c_0_58,negated_conjecture,
    ( k4_tarski(k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)),esk7_0) = esk7_0
    | k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0
    | k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])]),c_0_52]),c_0_53]),c_0_54])).

cnf(c_0_59,plain,
    ( k4_tarski(X1,X2) != X2 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_39])).

cnf(c_0_60,plain,
    ( esk3_1(k1_enumset1(X1,X1,X2)) = X1
    | X2 != k4_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_57,c_0_46])).

cnf(c_0_61,negated_conjecture,
    ( k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0
    | k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0 ),
    inference(sr,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_62,plain,
    ( esk3_1(k1_enumset1(X1,X1,k4_tarski(X1,X2))) = X1 ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( k4_tarski(k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),esk7_0),k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)) = esk7_0
    | k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_61]),c_0_51])]),c_0_52]),c_0_53]),c_0_54])).

cnf(c_0_64,plain,
    ( esk3_1(k1_enumset1(X1,X1,X2)) != k4_tarski(X3,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_32]),c_0_39])).

cnf(c_0_65,negated_conjecture,
    ( k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_66,negated_conjecture,
    ( k4_tarski(k4_tarski(esk7_0,k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)),k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)) = esk7_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_65]),c_0_51])]),c_0_52]),c_0_53]),c_0_54])).

cnf(c_0_67,plain,
    ( esk3_1(k1_enumset1(X1,X1,X2)) != k4_tarski(X2,X3) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_32]),c_0_39])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_66]),c_0_67]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:08:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.12/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.028 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.12/0.37  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.12/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.37  fof(t9_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_tarski(X3,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 0.12/0.37  fof(t72_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)<=>(~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 0.12/0.37  fof(t51_mcart_1, conjecture, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_mcart_1)).
% 0.12/0.37  fof(t48_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 0.12/0.37  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.12/0.37  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.12/0.37  fof(c_0_9, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.12/0.37  fof(c_0_10, plain, ![X14, X15, X16, X17, X18, X19, X20, X21]:(((~r2_hidden(X17,X16)|(X17=X14|X17=X15)|X16!=k2_tarski(X14,X15))&((X18!=X14|r2_hidden(X18,X16)|X16!=k2_tarski(X14,X15))&(X18!=X15|r2_hidden(X18,X16)|X16!=k2_tarski(X14,X15))))&(((esk2_3(X19,X20,X21)!=X19|~r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k2_tarski(X19,X20))&(esk2_3(X19,X20,X21)!=X20|~r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k2_tarski(X19,X20)))&(r2_hidden(esk2_3(X19,X20,X21),X21)|(esk2_3(X19,X20,X21)=X19|esk2_3(X19,X20,X21)=X20)|X21=k2_tarski(X19,X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.12/0.37  fof(c_0_11, plain, ![X23, X24]:k1_enumset1(X23,X23,X24)=k2_tarski(X23,X24), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.37  cnf(c_0_12, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  fof(c_0_13, plain, ![X38, X40, X41]:((r2_hidden(esk3_1(X38),X38)|X38=k1_xboole_0)&((~r2_hidden(X40,X38)|esk3_1(X38)!=k4_tarski(X40,X41)|X38=k1_xboole_0)&(~r2_hidden(X41,X38)|esk3_1(X38)!=k4_tarski(X40,X41)|X38=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).
% 0.12/0.37  cnf(c_0_14, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_15, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_16, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  fof(c_0_17, plain, ![X25, X26, X27]:(((~r2_hidden(X25,X27)|k4_xboole_0(k2_tarski(X25,X26),X27)!=k2_tarski(X25,X26))&(~r2_hidden(X26,X27)|k4_xboole_0(k2_tarski(X25,X26),X27)!=k2_tarski(X25,X26)))&(r2_hidden(X25,X27)|r2_hidden(X26,X27)|k4_xboole_0(k2_tarski(X25,X26),X27)=k2_tarski(X25,X26))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).
% 0.12/0.37  cnf(c_0_18, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_19, plain, (r2_hidden(esk3_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_20, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_14])).
% 0.12/0.37  cnf(c_0_21, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X4,X2)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.12/0.37  cnf(c_0_22, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_23, plain, (~r2_hidden(X1,X2)|k4_xboole_0(k2_tarski(X3,X1),X2)!=k2_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_24, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r2_hidden(esk3_1(k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.37  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk3_1(k4_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_20, c_0_19])).
% 0.12/0.37  cnf(c_0_26, plain, (r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X3,X1)), inference(er,[status(thm)],[c_0_21])).
% 0.12/0.37  cnf(c_0_27, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  fof(c_0_28, negated_conjecture, ~(![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4))))))), inference(assume_negation,[status(cth)],[t51_mcart_1])).
% 0.12/0.37  cnf(c_0_29, plain, (X1=X4|X1=X3|X2!=k1_enumset1(X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_16])).
% 0.12/0.37  cnf(c_0_30, plain, (k4_xboole_0(k1_enumset1(X3,X3,X1),X2)!=k1_enumset1(X3,X3,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_16]), c_0_16])).
% 0.12/0.37  cnf(c_0_31, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.12/0.37  cnf(c_0_32, plain, (r2_hidden(X1,k1_enumset1(X2,X2,X1))), inference(er,[status(thm)],[c_0_26])).
% 0.12/0.37  cnf(c_0_33, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X2,X4)), inference(rw,[status(thm)],[c_0_27, c_0_16])).
% 0.12/0.37  fof(c_0_34, plain, ![X34, X35, X36, X37]:(X34=k1_xboole_0|X35=k1_xboole_0|X36=k1_xboole_0|(~m1_subset_1(X37,k3_zfmisc_1(X34,X35,X36))|X37=k3_mcart_1(k5_mcart_1(X34,X35,X36,X37),k6_mcart_1(X34,X35,X36,X37),k7_mcart_1(X34,X35,X36,X37)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).
% 0.12/0.37  fof(c_0_35, plain, ![X28, X29, X30]:k3_mcart_1(X28,X29,X30)=k4_tarski(k4_tarski(X28,X29),X30), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.12/0.37  fof(c_0_36, plain, ![X31, X32, X33]:k3_zfmisc_1(X31,X32,X33)=k2_zfmisc_1(k2_zfmisc_1(X31,X32),X33), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.12/0.37  fof(c_0_37, negated_conjecture, (((esk4_0!=k1_xboole_0&esk5_0!=k1_xboole_0)&esk6_0!=k1_xboole_0)&(m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))&(esk7_0=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|esk7_0=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|esk7_0=k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).
% 0.12/0.37  cnf(c_0_38, plain, (X1=X2|X1=X3|~r2_hidden(X1,k1_enumset1(X2,X2,X3))), inference(er,[status(thm)],[c_0_29])).
% 0.12/0.37  cnf(c_0_39, plain, (k1_enumset1(X1,X1,X2)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 0.12/0.37  cnf(c_0_40, plain, (r2_hidden(X1,X2)|X2!=k1_enumset1(X1,X1,X3)), inference(er,[status(thm)],[c_0_33])).
% 0.12/0.37  cnf(c_0_41, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.37  cnf(c_0_42, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.37  cnf(c_0_43, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.37  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.12/0.37  cnf(c_0_45, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk3_1(X2)!=k4_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_46, plain, (esk3_1(k1_enumset1(X1,X1,X2))=X2|esk3_1(k1_enumset1(X1,X1,X2))=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_19]), c_0_39])).
% 0.12/0.37  cnf(c_0_47, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk3_1(X2)!=k4_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_48, plain, (r2_hidden(X1,k1_enumset1(X1,X1,X2))), inference(er,[status(thm)],[c_0_40])).
% 0.12/0.37  cnf(c_0_49, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X4=k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.12/0.37  cnf(c_0_50, negated_conjecture, (esk7_0=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|esk7_0=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|esk7_0=k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.12/0.37  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk7_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[c_0_44, c_0_43])).
% 0.12/0.37  cnf(c_0_52, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.12/0.37  cnf(c_0_53, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.12/0.37  cnf(c_0_54, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.12/0.37  cnf(c_0_55, plain, (X1=k1_xboole_0|k4_tarski(X2,esk3_1(X1))!=esk3_1(X1)), inference(spm,[status(thm)],[c_0_45, c_0_19])).
% 0.12/0.37  cnf(c_0_56, plain, (esk3_1(k1_enumset1(X1,X1,X1))=X1), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_46])])).
% 0.12/0.37  cnf(c_0_57, plain, (esk3_1(k1_enumset1(X1,X1,X2))!=k4_tarski(X1,X3)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_39])).
% 0.12/0.37  cnf(c_0_58, negated_conjecture, (k4_tarski(k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)),esk7_0)=esk7_0|k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0|k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])]), c_0_52]), c_0_53]), c_0_54])).
% 0.12/0.37  cnf(c_0_59, plain, (k4_tarski(X1,X2)!=X2), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_39])).
% 0.12/0.37  cnf(c_0_60, plain, (esk3_1(k1_enumset1(X1,X1,X2))=X1|X2!=k4_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_57, c_0_46])).
% 0.12/0.37  cnf(c_0_61, negated_conjecture, (k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0|k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0), inference(sr,[status(thm)],[c_0_58, c_0_59])).
% 0.12/0.37  cnf(c_0_62, plain, (esk3_1(k1_enumset1(X1,X1,k4_tarski(X1,X2)))=X1), inference(er,[status(thm)],[c_0_60])).
% 0.12/0.37  cnf(c_0_63, negated_conjecture, (k4_tarski(k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),esk7_0),k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0))=esk7_0|k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_61]), c_0_51])]), c_0_52]), c_0_53]), c_0_54])).
% 0.12/0.37  cnf(c_0_64, plain, (esk3_1(k1_enumset1(X1,X1,X2))!=k4_tarski(X3,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_32]), c_0_39])).
% 0.12/0.37  cnf(c_0_65, negated_conjecture, (k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.12/0.37  cnf(c_0_66, negated_conjecture, (k4_tarski(k4_tarski(esk7_0,k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)),k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0))=esk7_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_65]), c_0_51])]), c_0_52]), c_0_53]), c_0_54])).
% 0.12/0.37  cnf(c_0_67, plain, (esk3_1(k1_enumset1(X1,X1,X2))!=k4_tarski(X2,X3)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_32]), c_0_39])).
% 0.12/0.37  cnf(c_0_68, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_66]), c_0_67]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 69
% 0.12/0.37  # Proof object clause steps            : 50
% 0.12/0.37  # Proof object formula steps           : 19
% 0.12/0.37  # Proof object conjectures             : 15
% 0.12/0.37  # Proof object clause conjectures      : 12
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 18
% 0.12/0.37  # Proof object initial formulas used   : 9
% 0.12/0.37  # Proof object generating inferences   : 23
% 0.12/0.37  # Proof object simplifying inferences  : 36
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 9
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 27
% 0.12/0.37  # Removed in clause preprocessing      : 3
% 0.12/0.37  # Initial clauses in saturation        : 24
% 0.12/0.37  # Processed clauses                    : 200
% 0.12/0.37  # ...of these trivial                  : 10
% 0.12/0.37  # ...subsumed                          : 72
% 0.12/0.37  # ...remaining for further processing  : 118
% 0.12/0.37  # Other redundant clauses eliminated   : 17
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 1
% 0.12/0.37  # Backward-rewritten                   : 3
% 0.12/0.37  # Generated clauses                    : 450
% 0.12/0.37  # ...of the previous two non-trivial   : 323
% 0.12/0.37  # Contextual simplify-reflections      : 3
% 0.12/0.37  # Paramodulations                      : 410
% 0.12/0.37  # Factorizations                       : 10
% 0.12/0.37  # Equation resolutions                 : 29
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 87
% 0.12/0.37  #    Positive orientable unit clauses  : 12
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 11
% 0.12/0.37  #    Non-unit-clauses                  : 64
% 0.12/0.37  # Current number of unprocessed clauses: 169
% 0.12/0.37  # ...number of literals in the above   : 585
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 32
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 758
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 554
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 33
% 0.12/0.37  # Unit Clause-clause subsumption calls : 175
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 19
% 0.12/0.37  # BW rewrite match successes           : 1
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 6406
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.037 s
% 0.12/0.37  # System time              : 0.004 s
% 0.12/0.37  # Total time               : 0.042 s
% 0.12/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
