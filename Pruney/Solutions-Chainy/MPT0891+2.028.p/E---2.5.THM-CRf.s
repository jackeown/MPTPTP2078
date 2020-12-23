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
% DateTime   : Thu Dec  3 10:59:56 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 (1492 expanded)
%              Number of clauses        :   64 ( 640 expanded)
%              Number of leaves         :   16 ( 376 expanded)
%              Depth                    :   13
%              Number of atoms          :  259 (5045 expanded)
%              Number of equality atoms :  191 (3986 expanded)
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

fof(t72_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    <=> ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

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

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

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

fof(t20_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(c_0_16,negated_conjecture,(
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

fof(c_0_17,plain,(
    ! [X10,X11,X12,X13,X14,X15,X16,X17] :
      ( ( ~ r2_hidden(X13,X12)
        | X13 = X10
        | X13 = X11
        | X12 != k2_tarski(X10,X11) )
      & ( X14 != X10
        | r2_hidden(X14,X12)
        | X12 != k2_tarski(X10,X11) )
      & ( X14 != X11
        | r2_hidden(X14,X12)
        | X12 != k2_tarski(X10,X11) )
      & ( esk1_3(X15,X16,X17) != X15
        | ~ r2_hidden(esk1_3(X15,X16,X17),X17)
        | X17 = k2_tarski(X15,X16) )
      & ( esk1_3(X15,X16,X17) != X16
        | ~ r2_hidden(esk1_3(X15,X16,X17),X17)
        | X17 = k2_tarski(X15,X16) )
      & ( r2_hidden(esk1_3(X15,X16,X17),X17)
        | esk1_3(X15,X16,X17) = X15
        | esk1_3(X15,X16,X17) = X16
        | X17 = k2_tarski(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_18,plain,(
    ! [X20,X21] : k1_enumset1(X20,X20,X21) = k2_tarski(X20,X21) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X24,X25,X26] :
      ( ( ~ r2_hidden(X24,X26)
        | k4_xboole_0(k2_tarski(X24,X25),X26) != k2_tarski(X24,X25) )
      & ( ~ r2_hidden(X25,X26)
        | k4_xboole_0(k2_tarski(X24,X25),X26) != k2_tarski(X24,X25) )
      & ( r2_hidden(X24,X26)
        | r2_hidden(X25,X26)
        | k4_xboole_0(k2_tarski(X24,X25),X26) = k2_tarski(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).

fof(c_0_20,plain,(
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

fof(c_0_21,plain,(
    ! [X30,X31,X32] : k3_zfmisc_1(X30,X31,X32) = k2_zfmisc_1(k2_zfmisc_1(X30,X31),X32) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_22,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & esk5_0 != k1_xboole_0
    & m1_subset_1(esk6_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0))
    & ( esk6_0 = k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)
      | esk6_0 = k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)
      | esk6_0 = k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_23,plain,(
    ! [X22,X23] :
      ( ( k4_xboole_0(X22,k1_tarski(X23)) != X22
        | ~ r2_hidden(X23,X22) )
      & ( r2_hidden(X23,X22)
        | k4_xboole_0(X22,k1_tarski(X23)) = X22 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_24,plain,(
    ! [X19] : k2_tarski(X19,X19) = k1_tarski(X19) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,X2)
    | k4_xboole_0(k2_tarski(X3,X1),X2) != k2_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,plain,(
    ! [X7] : k4_xboole_0(X7,k1_xboole_0) = X7 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_29,plain,(
    ! [X6] : k3_xboole_0(X6,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_30,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(X8,X9)) = k3_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_31,plain,(
    ! [X41,X42,X43,X44] :
      ( X41 = k1_xboole_0
      | X42 = k1_xboole_0
      | X43 = k1_xboole_0
      | ~ m1_subset_1(X44,k3_zfmisc_1(X41,X42,X43))
      | X44 = k3_mcart_1(k5_mcart_1(X41,X42,X43,X44),k6_mcart_1(X41,X42,X43,X44),k7_mcart_1(X41,X42,X43,X44)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).

fof(c_0_32,plain,(
    ! [X27,X28,X29] : k3_mcart_1(X27,X28,X29) = k4_tarski(k4_tarski(X27,X28),X29) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_33,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk6_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(X2,k1_tarski(X1)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X4,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_39,plain,(
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

cnf(c_0_40,plain,
    ( k4_xboole_0(k1_enumset1(X3,X3,X1),X2) != k1_enumset1(X3,X3,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_26]),c_0_26])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_44,plain,(
    ! [X33,X34,X35] :
      ( ( X33 != k1_mcart_1(X33)
        | X33 != k4_tarski(X34,X35) )
      & ( X33 != k2_mcart_1(X33)
        | X33 != k4_tarski(X34,X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk6_0,k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_34])).

cnf(c_0_49,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_50,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_51,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_52,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X2,k1_enumset1(X1,X1,X1)) = X2
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_26])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_38])])).

cnf(c_0_55,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_59,plain,
    ( X1 != k2_mcart_1(X1)
    | X1 != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_60,plain,(
    ! [X49,X50] :
      ( k1_mcart_1(k4_tarski(X49,X50)) = X49
      & k2_mcart_1(k4_tarski(X49,X50)) = X50 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_61,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk2_1(X2) != k3_mcart_1(X3,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_62,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_34])).

cnf(c_0_63,negated_conjecture,
    ( k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = k2_mcart_1(esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50]),c_0_51])).

cnf(c_0_64,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k1_enumset1(X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_52,c_0_26])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X2,X3))
    | ~ r2_hidden(X3,k1_enumset1(X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_53])).

cnf(c_0_66,plain,
    ( r2_hidden(esk2_1(k1_enumset1(X1,X1,X2)),k1_enumset1(X1,X1,X2)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_67,plain,
    ( k4_xboole_0(X1,k1_enumset1(X2,X2,X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_37]),c_0_26])).

cnf(c_0_68,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_58,c_0_41])).

cnf(c_0_69,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) != k4_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_70,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_71,plain,
    ( X2 = k1_xboole_0
    | esk2_1(X2) != k4_tarski(k4_tarski(X3,X1),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_61,c_0_46])).

cnf(c_0_72,negated_conjecture,
    ( k4_tarski(k4_tarski(k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)),k2_mcart_1(esk6_0)) = esk6_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_48]),c_0_63]),c_0_49]),c_0_50]),c_0_51])).

cnf(c_0_73,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k1_enumset1(X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_64])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X2,esk2_1(k1_enumset1(X1,X1,X1)))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_75,plain,
    ( k1_enumset1(X1,X1,X1) != k1_xboole_0
    | ~ r2_hidden(X1,k1_enumset1(X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( esk6_0 = k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)
    | esk6_0 = k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)
    | esk6_0 = k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_77,plain,
    ( k4_tarski(X1,X2) != X2 ),
    inference(rw,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_79,negated_conjecture,
    ( X1 = k1_xboole_0
    | esk2_1(X1) != esk6_0
    | ~ r2_hidden(k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_80,plain,
    ( esk2_1(k1_enumset1(X1,X1,X1)) = X1
    | X1 = X2 ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_81,plain,
    ( k1_enumset1(X1,X1,X1) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_54])])).

cnf(c_0_82,negated_conjecture,
    ( k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = esk6_0
    | k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = esk6_0
    | k2_mcart_1(esk6_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_76,c_0_63])).

cnf(c_0_83,negated_conjecture,
    ( k2_mcart_1(esk6_0) != esk6_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_72])).

cnf(c_0_84,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X2,X4) ),
    inference(rw,[status(thm)],[c_0_78,c_0_26])).

cnf(c_0_85,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk2_1(X2) != k3_mcart_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_86,negated_conjecture,
    ( esk6_0 = X1
    | ~ r2_hidden(k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),k1_enumset1(esk6_0,esk6_0,esk6_0)) ),
    inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])])).

cnf(c_0_87,negated_conjecture,
    ( k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = esk6_0
    | k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = esk6_0 ),
    inference(sr,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_88,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_84])])).

cnf(c_0_89,plain,
    ( X2 = k1_xboole_0
    | esk2_1(X2) != k4_tarski(k4_tarski(X1,X3),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_85,c_0_46])).

cnf(c_0_90,plain,
    ( k1_enumset1(X1,X1,X2) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_68]),c_0_54])])).

cnf(c_0_91,negated_conjecture,
    ( k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = esk6_0
    | esk6_0 = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88])])).

cnf(c_0_92,negated_conjecture,
    ( X1 = k1_xboole_0
    | esk2_1(X1) != esk6_0
    | ~ r2_hidden(k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_72])).

cnf(c_0_93,negated_conjecture,
    ( k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = esk6_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_91])).

cnf(c_0_94,negated_conjecture,
    ( X1 = k1_xboole_0
    | esk2_1(X1) != esk6_0
    | ~ r2_hidden(esk6_0,X1) ),
    inference(rw,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_95,negated_conjecture,
    ( esk6_0 = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_80]),c_0_81])]),c_0_88])])).

cnf(c_0_96,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_95]),c_0_95]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:55:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.20/0.43  # and selection function SelectNegativeLiterals.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.028 s
% 0.20/0.43  # Presaturation interreduction done
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(t51_mcart_1, conjecture, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_mcart_1)).
% 0.20/0.43  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.20/0.43  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.43  fof(t72_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)<=>(~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 0.20/0.43  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.20/0.43  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.20/0.43  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.20/0.43  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.43  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.20/0.43  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.20/0.43  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.43  fof(t48_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 0.20/0.43  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.20/0.43  fof(t29_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k3_mcart_1(X3,X4,X5))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 0.20/0.43  fof(t20_mcart_1, axiom, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.20/0.43  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.20/0.43  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4))))))), inference(assume_negation,[status(cth)],[t51_mcart_1])).
% 0.20/0.43  fof(c_0_17, plain, ![X10, X11, X12, X13, X14, X15, X16, X17]:(((~r2_hidden(X13,X12)|(X13=X10|X13=X11)|X12!=k2_tarski(X10,X11))&((X14!=X10|r2_hidden(X14,X12)|X12!=k2_tarski(X10,X11))&(X14!=X11|r2_hidden(X14,X12)|X12!=k2_tarski(X10,X11))))&(((esk1_3(X15,X16,X17)!=X15|~r2_hidden(esk1_3(X15,X16,X17),X17)|X17=k2_tarski(X15,X16))&(esk1_3(X15,X16,X17)!=X16|~r2_hidden(esk1_3(X15,X16,X17),X17)|X17=k2_tarski(X15,X16)))&(r2_hidden(esk1_3(X15,X16,X17),X17)|(esk1_3(X15,X16,X17)=X15|esk1_3(X15,X16,X17)=X16)|X17=k2_tarski(X15,X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.20/0.43  fof(c_0_18, plain, ![X20, X21]:k1_enumset1(X20,X20,X21)=k2_tarski(X20,X21), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.43  fof(c_0_19, plain, ![X24, X25, X26]:(((~r2_hidden(X24,X26)|k4_xboole_0(k2_tarski(X24,X25),X26)!=k2_tarski(X24,X25))&(~r2_hidden(X25,X26)|k4_xboole_0(k2_tarski(X24,X25),X26)!=k2_tarski(X24,X25)))&(r2_hidden(X24,X26)|r2_hidden(X25,X26)|k4_xboole_0(k2_tarski(X24,X25),X26)=k2_tarski(X24,X25))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).
% 0.20/0.43  fof(c_0_20, plain, ![X45, X46, X47, X48]:(((k5_mcart_1(X45,X46,X47,X48)=k1_mcart_1(k1_mcart_1(X48))|~m1_subset_1(X48,k3_zfmisc_1(X45,X46,X47))|(X45=k1_xboole_0|X46=k1_xboole_0|X47=k1_xboole_0))&(k6_mcart_1(X45,X46,X47,X48)=k2_mcart_1(k1_mcart_1(X48))|~m1_subset_1(X48,k3_zfmisc_1(X45,X46,X47))|(X45=k1_xboole_0|X46=k1_xboole_0|X47=k1_xboole_0)))&(k7_mcart_1(X45,X46,X47,X48)=k2_mcart_1(X48)|~m1_subset_1(X48,k3_zfmisc_1(X45,X46,X47))|(X45=k1_xboole_0|X46=k1_xboole_0|X47=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.20/0.43  fof(c_0_21, plain, ![X30, X31, X32]:k3_zfmisc_1(X30,X31,X32)=k2_zfmisc_1(k2_zfmisc_1(X30,X31),X32), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.20/0.43  fof(c_0_22, negated_conjecture, (((esk3_0!=k1_xboole_0&esk4_0!=k1_xboole_0)&esk5_0!=k1_xboole_0)&(m1_subset_1(esk6_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0))&(esk6_0=k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)|esk6_0=k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)|esk6_0=k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.20/0.43  fof(c_0_23, plain, ![X22, X23]:((k4_xboole_0(X22,k1_tarski(X23))!=X22|~r2_hidden(X23,X22))&(r2_hidden(X23,X22)|k4_xboole_0(X22,k1_tarski(X23))=X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.20/0.43  fof(c_0_24, plain, ![X19]:k2_tarski(X19,X19)=k1_tarski(X19), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.43  cnf(c_0_25, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.43  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.43  cnf(c_0_27, plain, (~r2_hidden(X1,X2)|k4_xboole_0(k2_tarski(X3,X1),X2)!=k2_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  fof(c_0_28, plain, ![X7]:k4_xboole_0(X7,k1_xboole_0)=X7, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.20/0.43  fof(c_0_29, plain, ![X6]:k3_xboole_0(X6,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.20/0.43  fof(c_0_30, plain, ![X8, X9]:k4_xboole_0(X8,k4_xboole_0(X8,X9))=k3_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.43  fof(c_0_31, plain, ![X41, X42, X43, X44]:(X41=k1_xboole_0|X42=k1_xboole_0|X43=k1_xboole_0|(~m1_subset_1(X44,k3_zfmisc_1(X41,X42,X43))|X44=k3_mcart_1(k5_mcart_1(X41,X42,X43,X44),k6_mcart_1(X41,X42,X43,X44),k7_mcart_1(X41,X42,X43,X44)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).
% 0.20/0.43  fof(c_0_32, plain, ![X27, X28, X29]:k3_mcart_1(X27,X28,X29)=k4_tarski(k4_tarski(X27,X28),X29), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.20/0.43  cnf(c_0_33, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.43  cnf(c_0_34, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.43  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk6_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.43  cnf(c_0_36, plain, (r2_hidden(X1,X2)|k4_xboole_0(X2,k1_tarski(X1))=X2), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.43  cnf(c_0_37, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.43  cnf(c_0_38, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X4,X2)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.43  fof(c_0_39, plain, ![X36, X38, X39, X40]:((r2_hidden(esk2_1(X36),X36)|X36=k1_xboole_0)&((~r2_hidden(X38,X36)|esk2_1(X36)!=k3_mcart_1(X38,X39,X40)|X36=k1_xboole_0)&(~r2_hidden(X39,X36)|esk2_1(X36)!=k3_mcart_1(X38,X39,X40)|X36=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).
% 0.20/0.43  cnf(c_0_40, plain, (k4_xboole_0(k1_enumset1(X3,X3,X1),X2)!=k1_enumset1(X3,X3,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_26]), c_0_26])).
% 0.20/0.43  cnf(c_0_41, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.43  cnf(c_0_42, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.43  cnf(c_0_43, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.43  fof(c_0_44, plain, ![X33, X34, X35]:((X33!=k1_mcart_1(X33)|X33!=k4_tarski(X34,X35))&(X33!=k2_mcart_1(X33)|X33!=k4_tarski(X34,X35))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).
% 0.20/0.43  cnf(c_0_45, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.43  cnf(c_0_46, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.43  cnf(c_0_47, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.43  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk6_0,k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0))), inference(rw,[status(thm)],[c_0_35, c_0_34])).
% 0.20/0.43  cnf(c_0_49, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.43  cnf(c_0_50, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.43  cnf(c_0_51, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.43  cnf(c_0_52, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.43  cnf(c_0_53, plain, (k4_xboole_0(X2,k1_enumset1(X1,X1,X1))=X2|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_26])).
% 0.20/0.43  cnf(c_0_54, plain, (r2_hidden(X1,k1_enumset1(X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_38])])).
% 0.20/0.43  cnf(c_0_55, plain, (r2_hidden(esk2_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.43  cnf(c_0_56, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.43  cnf(c_0_57, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.43  cnf(c_0_58, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.43  cnf(c_0_59, plain, (X1!=k2_mcart_1(X1)|X1!=k4_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.43  fof(c_0_60, plain, ![X49, X50]:(k1_mcart_1(k4_tarski(X49,X50))=X49&k2_mcart_1(k4_tarski(X49,X50))=X50), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.20/0.43  cnf(c_0_61, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk2_1(X2)!=k3_mcart_1(X3,X1,X4)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.43  cnf(c_0_62, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X4=k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_34])).
% 0.20/0.43  cnf(c_0_63, negated_conjecture, (k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=k2_mcart_1(esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_50]), c_0_51])).
% 0.20/0.43  cnf(c_0_64, plain, (X1=X4|X1=X3|X2!=k1_enumset1(X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_52, c_0_26])).
% 0.20/0.43  cnf(c_0_65, plain, (r2_hidden(X1,k1_enumset1(X2,X2,X3))|~r2_hidden(X3,k1_enumset1(X1,X1,X1))), inference(spm,[status(thm)],[c_0_40, c_0_53])).
% 0.20/0.43  cnf(c_0_66, plain, (r2_hidden(esk2_1(k1_enumset1(X1,X1,X2)),k1_enumset1(X1,X1,X2))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 0.20/0.43  cnf(c_0_67, plain, (k4_xboole_0(X1,k1_enumset1(X2,X2,X2))!=X1|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_37]), c_0_26])).
% 0.20/0.43  cnf(c_0_68, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_58, c_0_41])).
% 0.20/0.43  cnf(c_0_69, plain, (k2_mcart_1(k4_tarski(X1,X2))!=k4_tarski(X1,X2)), inference(er,[status(thm)],[c_0_59])).
% 0.20/0.43  cnf(c_0_70, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.43  cnf(c_0_71, plain, (X2=k1_xboole_0|esk2_1(X2)!=k4_tarski(k4_tarski(X3,X1),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_61, c_0_46])).
% 0.20/0.43  cnf(c_0_72, negated_conjecture, (k4_tarski(k4_tarski(k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)),k2_mcart_1(esk6_0))=esk6_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_48]), c_0_63]), c_0_49]), c_0_50]), c_0_51])).
% 0.20/0.43  cnf(c_0_73, plain, (X1=X2|X1=X3|~r2_hidden(X1,k1_enumset1(X3,X3,X2))), inference(er,[status(thm)],[c_0_64])).
% 0.20/0.43  cnf(c_0_74, plain, (r2_hidden(X1,k1_enumset1(X2,X2,esk2_1(k1_enumset1(X1,X1,X1))))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.43  cnf(c_0_75, plain, (k1_enumset1(X1,X1,X1)!=k1_xboole_0|~r2_hidden(X1,k1_enumset1(X1,X1,X1))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.20/0.43  cnf(c_0_76, negated_conjecture, (esk6_0=k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)|esk6_0=k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)|esk6_0=k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.43  cnf(c_0_77, plain, (k4_tarski(X1,X2)!=X2), inference(rw,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.43  cnf(c_0_78, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.43  cnf(c_0_79, negated_conjecture, (X1=k1_xboole_0|esk2_1(X1)!=esk6_0|~r2_hidden(k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.43  cnf(c_0_80, plain, (esk2_1(k1_enumset1(X1,X1,X1))=X1|X1=X2), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.20/0.43  cnf(c_0_81, plain, (k1_enumset1(X1,X1,X1)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_54])])).
% 0.20/0.43  cnf(c_0_82, negated_conjecture, (k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=esk6_0|k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=esk6_0|k2_mcart_1(esk6_0)=esk6_0), inference(spm,[status(thm)],[c_0_76, c_0_63])).
% 0.20/0.43  cnf(c_0_83, negated_conjecture, (k2_mcart_1(esk6_0)!=esk6_0), inference(spm,[status(thm)],[c_0_77, c_0_72])).
% 0.20/0.43  cnf(c_0_84, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X2,X4)), inference(rw,[status(thm)],[c_0_78, c_0_26])).
% 0.20/0.43  cnf(c_0_85, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk2_1(X2)!=k3_mcart_1(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.43  cnf(c_0_86, negated_conjecture, (esk6_0=X1|~r2_hidden(k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),k1_enumset1(esk6_0,esk6_0,esk6_0))), inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])])).
% 0.20/0.43  cnf(c_0_87, negated_conjecture, (k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=esk6_0|k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=esk6_0), inference(sr,[status(thm)],[c_0_82, c_0_83])).
% 0.20/0.43  cnf(c_0_88, plain, (r2_hidden(X1,k1_enumset1(X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_84])])).
% 0.20/0.43  cnf(c_0_89, plain, (X2=k1_xboole_0|esk2_1(X2)!=k4_tarski(k4_tarski(X1,X3),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_85, c_0_46])).
% 0.20/0.43  cnf(c_0_90, plain, (k1_enumset1(X1,X1,X2)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_68]), c_0_54])])).
% 0.20/0.43  cnf(c_0_91, negated_conjecture, (k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=esk6_0|esk6_0=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88])])).
% 0.20/0.43  cnf(c_0_92, negated_conjecture, (X1=k1_xboole_0|esk2_1(X1)!=esk6_0|~r2_hidden(k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_89, c_0_72])).
% 0.20/0.43  cnf(c_0_93, negated_conjecture, (k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=esk6_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_91])).
% 0.20/0.43  cnf(c_0_94, negated_conjecture, (X1=k1_xboole_0|esk2_1(X1)!=esk6_0|~r2_hidden(esk6_0,X1)), inference(rw,[status(thm)],[c_0_92, c_0_93])).
% 0.20/0.43  cnf(c_0_95, negated_conjecture, (esk6_0=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_80]), c_0_81])]), c_0_88])])).
% 0.20/0.43  cnf(c_0_96, plain, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_95]), c_0_95]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 97
% 0.20/0.43  # Proof object clause steps            : 64
% 0.20/0.43  # Proof object formula steps           : 33
% 0.20/0.43  # Proof object conjectures             : 21
% 0.20/0.43  # Proof object clause conjectures      : 18
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 25
% 0.20/0.43  # Proof object initial formulas used   : 16
% 0.20/0.43  # Proof object generating inferences   : 17
% 0.20/0.43  # Proof object simplifying inferences  : 49
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 16
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 34
% 0.20/0.43  # Removed in clause preprocessing      : 5
% 0.20/0.43  # Initial clauses in saturation        : 29
% 0.20/0.43  # Processed clauses                    : 449
% 0.20/0.43  # ...of these trivial                  : 16
% 0.20/0.43  # ...subsumed                          : 208
% 0.20/0.43  # ...remaining for further processing  : 225
% 0.20/0.43  # Other redundant clauses eliminated   : 374
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 6
% 0.20/0.43  # Backward-rewritten                   : 180
% 0.20/0.43  # Generated clauses                    : 3815
% 0.20/0.43  # ...of the previous two non-trivial   : 2796
% 0.20/0.43  # Contextual simplify-reflections      : 1
% 0.20/0.43  # Paramodulations                      : 3432
% 0.20/0.43  # Factorizations                       : 8
% 0.20/0.43  # Equation resolutions                 : 374
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 2
% 0.20/0.43  #    Positive orientable unit clauses  : 0
% 0.20/0.43  #    Positive unorientable unit clauses: 1
% 0.20/0.43  #    Negative unit clauses             : 1
% 0.20/0.43  #    Non-unit-clauses                  : 0
% 0.20/0.43  # Current number of unprocessed clauses: 2355
% 0.20/0.43  # ...number of literals in the above   : 8171
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 223
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 2246
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 1454
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 173
% 0.20/0.43  # Unit Clause-clause subsumption calls : 184
% 0.20/0.43  # Rewrite failures with RHS unbound    : 5
% 0.20/0.43  # BW rewrite match attempts            : 146
% 0.20/0.43  # BW rewrite match successes           : 130
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 50883
% 0.20/0.44  
% 0.20/0.44  # -------------------------------------------------
% 0.20/0.44  # User time                : 0.077 s
% 0.20/0.44  # System time              : 0.007 s
% 0.20/0.44  # Total time               : 0.084 s
% 0.20/0.44  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
