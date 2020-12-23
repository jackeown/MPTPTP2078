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
% DateTime   : Thu Dec  3 10:59:55 EST 2020

% Result     : Theorem 0.45s
% Output     : CNFRefutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 472 expanded)
%              Number of clauses        :   61 ( 205 expanded)
%              Number of leaves         :   17 ( 119 expanded)
%              Depth                    :   12
%              Number of atoms          :  282 (1579 expanded)
%              Number of equality atoms :  191 (1195 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

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

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

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

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t20_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(t72_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    <=> ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(c_0_17,plain,(
    ! [X31,X32,X33] :
      ( ( r2_hidden(X31,X32)
        | ~ r2_hidden(X31,k4_xboole_0(X32,k1_tarski(X33))) )
      & ( X31 != X33
        | ~ r2_hidden(X31,k4_xboole_0(X32,k1_tarski(X33))) )
      & ( ~ r2_hidden(X31,X32)
        | X31 = X33
        | r2_hidden(X31,k4_xboole_0(X32,k1_tarski(X33))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_18,plain,(
    ! [X28] : k2_tarski(X28,X28) = k1_tarski(X28) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_19,plain,(
    ! [X29,X30] : k1_enumset1(X29,X29,X30) = k2_tarski(X29,X30) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_20,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,negated_conjecture,(
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

cnf(c_0_24,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_enumset1(X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

fof(c_0_25,plain,(
    ! [X18] : k4_xboole_0(k1_xboole_0,X18) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_26,plain,(
    ! [X19,X20,X21,X22,X23,X24,X25,X26] :
      ( ( ~ r2_hidden(X22,X21)
        | X22 = X19
        | X22 = X20
        | X21 != k2_tarski(X19,X20) )
      & ( X23 != X19
        | r2_hidden(X23,X21)
        | X21 != k2_tarski(X19,X20) )
      & ( X23 != X20
        | r2_hidden(X23,X21)
        | X21 != k2_tarski(X19,X20) )
      & ( esk2_3(X24,X25,X26) != X24
        | ~ r2_hidden(esk2_3(X24,X25,X26),X26)
        | X26 = k2_tarski(X24,X25) )
      & ( esk2_3(X24,X25,X26) != X25
        | ~ r2_hidden(esk2_3(X24,X25,X26),X26)
        | X26 = k2_tarski(X24,X25) )
      & ( r2_hidden(esk2_3(X24,X25,X26),X26)
        | esk2_3(X24,X25,X26) = X24
        | esk2_3(X24,X25,X26) = X25
        | X26 = k2_tarski(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_27,plain,(
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

fof(c_0_28,plain,(
    ! [X40,X41,X42] : k3_zfmisc_1(X40,X41,X42) = k2_zfmisc_1(k2_zfmisc_1(X40,X41),X42) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_29,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    & esk5_0 != k1_xboole_0
    & esk6_0 != k1_xboole_0
    & m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
    & ( esk7_0 = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
      | esk7_0 = k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
      | esk7_0 = k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k1_enumset1(X1,X1,X1))) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
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

cnf(c_0_33,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_34,plain,(
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

fof(c_0_35,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_36,plain,(
    ! [X51,X52,X53,X54] :
      ( X51 = k1_xboole_0
      | X52 = k1_xboole_0
      | X53 = k1_xboole_0
      | ~ m1_subset_1(X54,k3_zfmisc_1(X51,X52,X53))
      | X54 = k3_mcart_1(k5_mcart_1(X51,X52,X53,X54),k6_mcart_1(X51,X52,X53,X54),k7_mcart_1(X51,X52,X53,X54)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).

fof(c_0_37,plain,(
    ! [X37,X38,X39] : k3_mcart_1(X37,X38,X39) = k4_tarski(k4_tarski(X37,X38),X39) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_38,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_43,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X4,X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_22])).

cnf(c_0_45,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_47,plain,(
    ! [X15] : k4_xboole_0(X15,k1_xboole_0) = X15 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_48,plain,(
    ! [X43,X44,X45] :
      ( ( X43 != k1_mcart_1(X43)
        | X43 != k4_tarski(X44,X45) )
      & ( X43 != k2_mcart_1(X43)
        | X43 != k4_tarski(X44,X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_50,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk7_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[c_0_40,c_0_39])).

cnf(c_0_53,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_54,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_55,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_56,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k1_enumset1(X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_41,c_0_22])).

cnf(c_0_57,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_44])])).

fof(c_0_59,plain,(
    ! [X34,X35,X36] :
      ( ( ~ r2_hidden(X34,X36)
        | k4_xboole_0(k2_tarski(X34,X35),X36) != k2_tarski(X34,X35) )
      & ( ~ r2_hidden(X35,X36)
        | k4_xboole_0(k2_tarski(X34,X35),X36) != k2_tarski(X34,X35) )
      & ( r2_hidden(X34,X36)
        | r2_hidden(X35,X36)
        | k4_xboole_0(k2_tarski(X34,X35),X36) = k2_tarski(X34,X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).

cnf(c_0_60,plain,
    ( X3 = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_61,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_62,plain,
    ( X1 != k2_mcart_1(X1)
    | X1 != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_63,plain,(
    ! [X59,X60] :
      ( k1_mcart_1(k4_tarski(X59,X60)) = X59
      & k2_mcart_1(k4_tarski(X59,X60)) = X60 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_64,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk3_1(X2) != k3_mcart_1(X3,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_65,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50]),c_0_39])).

cnf(c_0_66,negated_conjecture,
    ( k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = k2_mcart_1(esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_54]),c_0_55])).

cnf(c_0_67,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k1_enumset1(X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_68,plain,
    ( r2_hidden(esk3_1(k1_enumset1(X1,X1,X2)),k1_enumset1(X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_69,plain,
    ( ~ r2_hidden(X1,X2)
    | k4_xboole_0(k2_tarski(X3,X1),X2) != k2_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_70,plain,
    ( X1 = k4_xboole_0(X2,X2)
    | r2_hidden(esk1_3(X2,k1_xboole_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_42])).

cnf(c_0_71,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) != k4_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_72,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_73,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk3_1(X2) != k3_mcart_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_74,plain,
    ( X2 = k1_xboole_0
    | esk3_1(X2) != k4_tarski(k4_tarski(X3,X1),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_64,c_0_50])).

cnf(c_0_75,negated_conjecture,
    ( k4_tarski(k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)),k2_mcart_1(esk7_0)) = esk7_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_52]),c_0_66]),c_0_53]),c_0_54]),c_0_55])).

cnf(c_0_76,plain,
    ( esk3_1(k1_enumset1(X1,X1,X2)) = X2
    | esk3_1(k1_enumset1(X1,X1,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_77,plain,
    ( k4_xboole_0(k1_enumset1(X3,X3,X1),X2) != k1_enumset1(X3,X3,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_22]),c_0_22])).

cnf(c_0_78,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_70]),c_0_31]),c_0_31]),c_0_42])).

cnf(c_0_79,negated_conjecture,
    ( esk7_0 = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
    | esk7_0 = k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
    | esk7_0 = k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_80,plain,
    ( k4_tarski(X1,X2) != X2 ),
    inference(rw,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_81,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_82,plain,
    ( X2 = k1_xboole_0
    | esk3_1(X2) != k4_tarski(k4_tarski(X1,X3),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_73,c_0_50])).

cnf(c_0_83,negated_conjecture,
    ( X1 = k1_xboole_0
    | esk3_1(X1) != esk7_0
    | ~ r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_84,plain,
    ( esk3_1(k1_enumset1(X1,X1,X1)) = X1 ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_76])])).

cnf(c_0_85,plain,
    ( k1_enumset1(X1,X1,X2) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_58])])).

cnf(c_0_86,negated_conjecture,
    ( k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0
    | k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0
    | k2_mcart_1(esk7_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_79,c_0_66])).

cnf(c_0_87,negated_conjecture,
    ( k2_mcart_1(esk7_0) != esk7_0 ),
    inference(spm,[status(thm)],[c_0_80,c_0_75])).

cnf(c_0_88,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X2,X4) ),
    inference(rw,[status(thm)],[c_0_81,c_0_22])).

cnf(c_0_89,negated_conjecture,
    ( X1 = k1_xboole_0
    | esk3_1(X1) != esk7_0
    | ~ r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_75])).

cnf(c_0_90,negated_conjecture,
    ( ~ r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k1_enumset1(esk7_0,esk7_0,esk7_0)) ),
    inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85])])).

cnf(c_0_91,negated_conjecture,
    ( k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0
    | k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0 ),
    inference(sr,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_92,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_88])])).

cnf(c_0_93,negated_conjecture,
    ( ~ r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k1_enumset1(esk7_0,esk7_0,esk7_0)) ),
    inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_84]),c_0_85])])).

cnf(c_0_94,negated_conjecture,
    ( k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_92])])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_94]),c_0_92])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:22:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.45/0.62  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.45/0.62  # and selection function SelectNegativeLiterals.
% 0.45/0.62  #
% 0.45/0.62  # Preprocessing time       : 0.029 s
% 0.45/0.62  # Presaturation interreduction done
% 0.45/0.62  
% 0.45/0.62  # Proof found!
% 0.45/0.62  # SZS status Theorem
% 0.45/0.62  # SZS output start CNFRefutation
% 0.45/0.62  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.45/0.62  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.45/0.62  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.45/0.62  fof(t51_mcart_1, conjecture, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_mcart_1)).
% 0.45/0.62  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.45/0.62  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.45/0.62  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.45/0.62  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.45/0.62  fof(t29_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k3_mcart_1(X3,X4,X5))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 0.45/0.62  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.45/0.62  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.45/0.62  fof(t48_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 0.45/0.62  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.45/0.62  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.45/0.62  fof(t20_mcart_1, axiom, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.45/0.62  fof(t72_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)<=>(~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 0.45/0.62  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.45/0.62  fof(c_0_17, plain, ![X31, X32, X33]:(((r2_hidden(X31,X32)|~r2_hidden(X31,k4_xboole_0(X32,k1_tarski(X33))))&(X31!=X33|~r2_hidden(X31,k4_xboole_0(X32,k1_tarski(X33)))))&(~r2_hidden(X31,X32)|X31=X33|r2_hidden(X31,k4_xboole_0(X32,k1_tarski(X33))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.45/0.62  fof(c_0_18, plain, ![X28]:k2_tarski(X28,X28)=k1_tarski(X28), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.45/0.62  fof(c_0_19, plain, ![X29, X30]:k1_enumset1(X29,X29,X30)=k2_tarski(X29,X30), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.45/0.62  cnf(c_0_20, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.45/0.62  cnf(c_0_21, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.45/0.62  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.45/0.62  fof(c_0_23, negated_conjecture, ~(![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4))))))), inference(assume_negation,[status(cth)],[t51_mcart_1])).
% 0.45/0.62  cnf(c_0_24, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_enumset1(X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.45/0.62  fof(c_0_25, plain, ![X18]:k4_xboole_0(k1_xboole_0,X18)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.45/0.62  fof(c_0_26, plain, ![X19, X20, X21, X22, X23, X24, X25, X26]:(((~r2_hidden(X22,X21)|(X22=X19|X22=X20)|X21!=k2_tarski(X19,X20))&((X23!=X19|r2_hidden(X23,X21)|X21!=k2_tarski(X19,X20))&(X23!=X20|r2_hidden(X23,X21)|X21!=k2_tarski(X19,X20))))&(((esk2_3(X24,X25,X26)!=X24|~r2_hidden(esk2_3(X24,X25,X26),X26)|X26=k2_tarski(X24,X25))&(esk2_3(X24,X25,X26)!=X25|~r2_hidden(esk2_3(X24,X25,X26),X26)|X26=k2_tarski(X24,X25)))&(r2_hidden(esk2_3(X24,X25,X26),X26)|(esk2_3(X24,X25,X26)=X24|esk2_3(X24,X25,X26)=X25)|X26=k2_tarski(X24,X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.45/0.62  fof(c_0_27, plain, ![X55, X56, X57, X58]:(((k5_mcart_1(X55,X56,X57,X58)=k1_mcart_1(k1_mcart_1(X58))|~m1_subset_1(X58,k3_zfmisc_1(X55,X56,X57))|(X55=k1_xboole_0|X56=k1_xboole_0|X57=k1_xboole_0))&(k6_mcart_1(X55,X56,X57,X58)=k2_mcart_1(k1_mcart_1(X58))|~m1_subset_1(X58,k3_zfmisc_1(X55,X56,X57))|(X55=k1_xboole_0|X56=k1_xboole_0|X57=k1_xboole_0)))&(k7_mcart_1(X55,X56,X57,X58)=k2_mcart_1(X58)|~m1_subset_1(X58,k3_zfmisc_1(X55,X56,X57))|(X55=k1_xboole_0|X56=k1_xboole_0|X57=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.45/0.62  fof(c_0_28, plain, ![X40, X41, X42]:k3_zfmisc_1(X40,X41,X42)=k2_zfmisc_1(k2_zfmisc_1(X40,X41),X42), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.45/0.62  fof(c_0_29, negated_conjecture, (((esk4_0!=k1_xboole_0&esk5_0!=k1_xboole_0)&esk6_0!=k1_xboole_0)&(m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))&(esk7_0=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|esk7_0=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|esk7_0=k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.45/0.62  cnf(c_0_30, plain, (~r2_hidden(X1,k4_xboole_0(X2,k1_enumset1(X1,X1,X1)))), inference(er,[status(thm)],[c_0_24])).
% 0.45/0.62  cnf(c_0_31, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.45/0.62  fof(c_0_32, plain, ![X46, X48, X49, X50]:((r2_hidden(esk3_1(X46),X46)|X46=k1_xboole_0)&((~r2_hidden(X48,X46)|esk3_1(X46)!=k3_mcart_1(X48,X49,X50)|X46=k1_xboole_0)&(~r2_hidden(X49,X46)|esk3_1(X46)!=k3_mcart_1(X48,X49,X50)|X46=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).
% 0.45/0.62  cnf(c_0_33, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.45/0.62  fof(c_0_34, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k3_xboole_0(X6,X7))&(r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k3_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|~r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k3_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|~r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k3_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k3_xboole_0(X11,X12))&(r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k3_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.45/0.62  fof(c_0_35, plain, ![X16, X17]:k4_xboole_0(X16,k4_xboole_0(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.45/0.62  fof(c_0_36, plain, ![X51, X52, X53, X54]:(X51=k1_xboole_0|X52=k1_xboole_0|X53=k1_xboole_0|(~m1_subset_1(X54,k3_zfmisc_1(X51,X52,X53))|X54=k3_mcart_1(k5_mcart_1(X51,X52,X53,X54),k6_mcart_1(X51,X52,X53,X54),k7_mcart_1(X51,X52,X53,X54)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).
% 0.45/0.62  fof(c_0_37, plain, ![X37, X38, X39]:k3_mcart_1(X37,X38,X39)=k4_tarski(k4_tarski(X37,X38),X39), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.45/0.62  cnf(c_0_38, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.45/0.62  cnf(c_0_39, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.45/0.62  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.45/0.62  cnf(c_0_41, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.45/0.62  cnf(c_0_42, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.45/0.62  cnf(c_0_43, plain, (r2_hidden(esk3_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.45/0.62  cnf(c_0_44, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X4,X2)), inference(rw,[status(thm)],[c_0_33, c_0_22])).
% 0.45/0.62  cnf(c_0_45, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.45/0.62  cnf(c_0_46, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.45/0.62  fof(c_0_47, plain, ![X15]:k4_xboole_0(X15,k1_xboole_0)=X15, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.45/0.62  fof(c_0_48, plain, ![X43, X44, X45]:((X43!=k1_mcart_1(X43)|X43!=k4_tarski(X44,X45))&(X43!=k2_mcart_1(X43)|X43!=k4_tarski(X44,X45))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).
% 0.45/0.62  cnf(c_0_49, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.45/0.62  cnf(c_0_50, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.45/0.62  cnf(c_0_51, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.45/0.62  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk7_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[c_0_40, c_0_39])).
% 0.45/0.62  cnf(c_0_53, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.45/0.62  cnf(c_0_54, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.45/0.62  cnf(c_0_55, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.45/0.62  cnf(c_0_56, plain, (X1=X4|X1=X3|X2!=k1_enumset1(X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_41, c_0_22])).
% 0.45/0.62  cnf(c_0_57, plain, (r2_hidden(esk3_1(X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.45/0.62  cnf(c_0_58, plain, (r2_hidden(X1,k1_enumset1(X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_44])])).
% 0.45/0.62  fof(c_0_59, plain, ![X34, X35, X36]:(((~r2_hidden(X34,X36)|k4_xboole_0(k2_tarski(X34,X35),X36)!=k2_tarski(X34,X35))&(~r2_hidden(X35,X36)|k4_xboole_0(k2_tarski(X34,X35),X36)!=k2_tarski(X34,X35)))&(r2_hidden(X34,X36)|r2_hidden(X35,X36)|k4_xboole_0(k2_tarski(X34,X35),X36)=k2_tarski(X34,X35))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).
% 0.45/0.62  cnf(c_0_60, plain, (X3=k4_xboole_0(X1,k4_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.45/0.62  cnf(c_0_61, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.45/0.62  cnf(c_0_62, plain, (X1!=k2_mcart_1(X1)|X1!=k4_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.45/0.62  fof(c_0_63, plain, ![X59, X60]:(k1_mcart_1(k4_tarski(X59,X60))=X59&k2_mcart_1(k4_tarski(X59,X60))=X60), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.45/0.62  cnf(c_0_64, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk3_1(X2)!=k3_mcart_1(X3,X1,X4)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.45/0.62  cnf(c_0_65, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X4=k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50]), c_0_39])).
% 0.45/0.62  cnf(c_0_66, negated_conjecture, (k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=k2_mcart_1(esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_54]), c_0_55])).
% 0.45/0.62  cnf(c_0_67, plain, (X1=X2|X1=X3|~r2_hidden(X1,k1_enumset1(X3,X3,X2))), inference(er,[status(thm)],[c_0_56])).
% 0.45/0.62  cnf(c_0_68, plain, (r2_hidden(esk3_1(k1_enumset1(X1,X1,X2)),k1_enumset1(X1,X1,X2))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.45/0.62  cnf(c_0_69, plain, (~r2_hidden(X1,X2)|k4_xboole_0(k2_tarski(X3,X1),X2)!=k2_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.45/0.62  cnf(c_0_70, plain, (X1=k4_xboole_0(X2,X2)|r2_hidden(esk1_3(X2,k1_xboole_0,X1),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_42])).
% 0.45/0.62  cnf(c_0_71, plain, (k2_mcart_1(k4_tarski(X1,X2))!=k4_tarski(X1,X2)), inference(er,[status(thm)],[c_0_62])).
% 0.45/0.62  cnf(c_0_72, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.45/0.62  cnf(c_0_73, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk3_1(X2)!=k3_mcart_1(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.45/0.62  cnf(c_0_74, plain, (X2=k1_xboole_0|esk3_1(X2)!=k4_tarski(k4_tarski(X3,X1),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_64, c_0_50])).
% 0.45/0.62  cnf(c_0_75, negated_conjecture, (k4_tarski(k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)),k2_mcart_1(esk7_0))=esk7_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_52]), c_0_66]), c_0_53]), c_0_54]), c_0_55])).
% 0.45/0.62  cnf(c_0_76, plain, (esk3_1(k1_enumset1(X1,X1,X2))=X2|esk3_1(k1_enumset1(X1,X1,X2))=X1), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.45/0.62  cnf(c_0_77, plain, (k4_xboole_0(k1_enumset1(X3,X3,X1),X2)!=k1_enumset1(X3,X3,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_22]), c_0_22])).
% 0.45/0.62  cnf(c_0_78, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_70]), c_0_31]), c_0_31]), c_0_42])).
% 0.45/0.62  cnf(c_0_79, negated_conjecture, (esk7_0=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|esk7_0=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|esk7_0=k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.45/0.62  cnf(c_0_80, plain, (k4_tarski(X1,X2)!=X2), inference(rw,[status(thm)],[c_0_71, c_0_72])).
% 0.45/0.62  cnf(c_0_81, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.45/0.62  cnf(c_0_82, plain, (X2=k1_xboole_0|esk3_1(X2)!=k4_tarski(k4_tarski(X1,X3),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_73, c_0_50])).
% 0.45/0.62  cnf(c_0_83, negated_conjecture, (X1=k1_xboole_0|esk3_1(X1)!=esk7_0|~r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),X1)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.45/0.62  cnf(c_0_84, plain, (esk3_1(k1_enumset1(X1,X1,X1))=X1), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_76])])).
% 0.45/0.62  cnf(c_0_85, plain, (k1_enumset1(X1,X1,X2)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_58])])).
% 0.45/0.62  cnf(c_0_86, negated_conjecture, (k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0|k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0|k2_mcart_1(esk7_0)=esk7_0), inference(spm,[status(thm)],[c_0_79, c_0_66])).
% 0.45/0.62  cnf(c_0_87, negated_conjecture, (k2_mcart_1(esk7_0)!=esk7_0), inference(spm,[status(thm)],[c_0_80, c_0_75])).
% 0.45/0.62  cnf(c_0_88, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X2,X4)), inference(rw,[status(thm)],[c_0_81, c_0_22])).
% 0.45/0.62  cnf(c_0_89, negated_conjecture, (X1=k1_xboole_0|esk3_1(X1)!=esk7_0|~r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),X1)), inference(spm,[status(thm)],[c_0_82, c_0_75])).
% 0.45/0.62  cnf(c_0_90, negated_conjecture, (~r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k1_enumset1(esk7_0,esk7_0,esk7_0))), inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85])])).
% 0.45/0.62  cnf(c_0_91, negated_conjecture, (k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0|k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0), inference(sr,[status(thm)],[c_0_86, c_0_87])).
% 0.45/0.62  cnf(c_0_92, plain, (r2_hidden(X1,k1_enumset1(X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_88])])).
% 0.45/0.62  cnf(c_0_93, negated_conjecture, (~r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k1_enumset1(esk7_0,esk7_0,esk7_0))), inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_84]), c_0_85])])).
% 0.45/0.62  cnf(c_0_94, negated_conjecture, (k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_92])])).
% 0.45/0.62  cnf(c_0_95, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_94]), c_0_92])]), ['proof']).
% 0.45/0.62  # SZS output end CNFRefutation
% 0.45/0.62  # Proof object total steps             : 96
% 0.45/0.62  # Proof object clause steps            : 61
% 0.45/0.62  # Proof object formula steps           : 35
% 0.45/0.62  # Proof object conjectures             : 20
% 0.45/0.62  # Proof object clause conjectures      : 17
% 0.45/0.62  # Proof object formula conjectures     : 3
% 0.45/0.62  # Proof object initial clauses used    : 25
% 0.45/0.62  # Proof object initial formulas used   : 17
% 0.45/0.62  # Proof object generating inferences   : 17
% 0.45/0.62  # Proof object simplifying inferences  : 46
% 0.45/0.62  # Training examples: 0 positive, 0 negative
% 0.45/0.62  # Parsed axioms                        : 17
% 0.45/0.62  # Removed by relevancy pruning/SinE    : 0
% 0.45/0.62  # Initial clauses                      : 41
% 0.45/0.62  # Removed in clause preprocessing      : 5
% 0.45/0.62  # Initial clauses in saturation        : 36
% 0.45/0.62  # Processed clauses                    : 1233
% 0.45/0.62  # ...of these trivial                  : 74
% 0.45/0.62  # ...subsumed                          : 752
% 0.45/0.62  # ...remaining for further processing  : 407
% 0.45/0.62  # Other redundant clauses eliminated   : 2163
% 0.45/0.62  # Clauses deleted for lack of memory   : 0
% 0.45/0.62  # Backward-subsumed                    : 12
% 0.45/0.62  # Backward-rewritten                   : 44
% 0.45/0.62  # Generated clauses                    : 25457
% 0.45/0.62  # ...of the previous two non-trivial   : 19247
% 0.45/0.62  # Contextual simplify-reflections      : 0
% 0.45/0.62  # Paramodulations                      : 23291
% 0.45/0.62  # Factorizations                       : 4
% 0.45/0.62  # Equation resolutions                 : 2163
% 0.45/0.62  # Propositional unsat checks           : 0
% 0.45/0.62  #    Propositional check models        : 0
% 0.45/0.62  #    Propositional check unsatisfiable : 0
% 0.45/0.62  #    Propositional clauses             : 0
% 0.45/0.62  #    Propositional clauses after purity: 0
% 0.45/0.62  #    Propositional unsat core size     : 0
% 0.45/0.62  #    Propositional preprocessing time  : 0.000
% 0.45/0.62  #    Propositional encoding time       : 0.000
% 0.45/0.62  #    Propositional solver time         : 0.000
% 0.45/0.62  #    Success case prop preproc time    : 0.000
% 0.45/0.62  #    Success case prop encoding time   : 0.000
% 0.45/0.62  #    Success case prop solver time     : 0.000
% 0.45/0.62  # Current number of processed clauses  : 305
% 0.45/0.62  #    Positive orientable unit clauses  : 38
% 0.45/0.62  #    Positive unorientable unit clauses: 0
% 0.45/0.62  #    Negative unit clauses             : 13
% 0.45/0.62  #    Non-unit-clauses                  : 254
% 0.45/0.62  # Current number of unprocessed clauses: 17957
% 0.45/0.62  # ...number of literals in the above   : 60145
% 0.45/0.62  # Current number of archived formulas  : 0
% 0.45/0.62  # Current number of archived clauses   : 98
% 0.45/0.62  # Clause-clause subsumption calls (NU) : 12082
% 0.45/0.62  # Rec. Clause-clause subsumption calls : 7343
% 0.45/0.62  # Non-unit clause-clause subsumptions  : 676
% 0.45/0.62  # Unit Clause-clause subsumption calls : 478
% 0.45/0.62  # Rewrite failures with RHS unbound    : 0
% 0.45/0.62  # BW rewrite match attempts            : 64
% 0.45/0.62  # BW rewrite match successes           : 15
% 0.45/0.62  # Condensation attempts                : 0
% 0.45/0.62  # Condensation successes               : 0
% 0.45/0.62  # Termbank termtop insertions          : 381000
% 0.45/0.62  
% 0.45/0.62  # -------------------------------------------------
% 0.45/0.62  # User time                : 0.260 s
% 0.45/0.62  # System time              : 0.018 s
% 0.45/0.62  # Total time               : 0.277 s
% 0.45/0.62  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
