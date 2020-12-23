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

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 465 expanded)
%              Number of clauses        :   62 ( 198 expanded)
%              Number of leaves         :   16 ( 115 expanded)
%              Depth                    :   14
%              Number of atoms          :  235 (1677 expanded)
%              Number of equality atoms :  174 (1351 expanded)
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

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

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
    ! [X44,X45,X46,X47] :
      ( X44 = k1_xboole_0
      | X45 = k1_xboole_0
      | X46 = k1_xboole_0
      | ~ m1_subset_1(X47,k3_zfmisc_1(X44,X45,X46))
      | X47 = k3_mcart_1(k5_mcart_1(X44,X45,X46,X47),k6_mcart_1(X44,X45,X46,X47),k7_mcart_1(X44,X45,X46,X47)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).

fof(c_0_18,plain,(
    ! [X30,X31,X32] : k3_mcart_1(X30,X31,X32) = k4_tarski(k4_tarski(X30,X31),X32) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_19,plain,(
    ! [X33,X34,X35] : k3_zfmisc_1(X33,X34,X35) = k2_zfmisc_1(k2_zfmisc_1(X33,X34),X35) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_20,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & esk5_0 != k1_xboole_0
    & m1_subset_1(esk6_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0))
    & ( esk6_0 = k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)
      | esk6_0 = k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)
      | esk6_0 = k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_21,plain,(
    ! [X25,X26,X27] :
      ( ( r2_hidden(X25,X26)
        | ~ r2_hidden(X25,k4_xboole_0(X26,k1_tarski(X27))) )
      & ( X25 != X27
        | ~ r2_hidden(X25,k4_xboole_0(X26,k1_tarski(X27))) )
      & ( ~ r2_hidden(X25,X26)
        | X25 = X27
        | r2_hidden(X25,k4_xboole_0(X26,k1_tarski(X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_22,plain,(
    ! [X22] : k2_tarski(X22,X22) = k1_tarski(X22) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_23,plain,(
    ! [X23,X24] : k1_enumset1(X23,X23,X24) = k2_tarski(X23,X24) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_24,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk6_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X36,X37,X38] :
      ( ( X36 != k1_mcart_1(X36)
        | X36 != k4_tarski(X37,X38) )
      & ( X36 != k2_mcart_1(X36)
        | X36 != k4_tarski(X37,X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).

cnf(c_0_29,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_32,plain,(
    ! [X48,X49] :
      ( k1_mcart_1(k4_tarski(X48,X49)) = X48
      & k2_mcart_1(k4_tarski(X48,X49)) = X49 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_33,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk6_0,k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_36,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_38,plain,
    ( X1 != k2_mcart_1(X1)
    | X1 != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_enumset1(X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

fof(c_0_40,plain,(
    ! [X10] : k4_xboole_0(k1_xboole_0,X10) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_41,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( k4_tarski(k4_tarski(k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)),k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)) = esk6_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_43,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) != k4_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k1_enumset1(X1,X1,X1))) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_46,plain,(
    ! [X39,X41,X42,X43] :
      ( ( r2_hidden(esk2_1(X39),X39)
        | X39 = k1_xboole_0 )
      & ( ~ r2_hidden(X41,X39)
        | esk2_1(X39) != k3_mcart_1(X41,X42,X43)
        | X39 = k1_xboole_0 )
      & ( ~ r2_hidden(X42,X39)
        | esk2_1(X39) != k3_mcart_1(X41,X42,X43)
        | X39 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).

fof(c_0_47,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X15,X14)
        | X15 = X11
        | X15 = X12
        | X15 = X13
        | X14 != k1_enumset1(X11,X12,X13) )
      & ( X16 != X11
        | r2_hidden(X16,X14)
        | X14 != k1_enumset1(X11,X12,X13) )
      & ( X16 != X12
        | r2_hidden(X16,X14)
        | X14 != k1_enumset1(X11,X12,X13) )
      & ( X16 != X13
        | r2_hidden(X16,X14)
        | X14 != k1_enumset1(X11,X12,X13) )
      & ( esk1_4(X17,X18,X19,X20) != X17
        | ~ r2_hidden(esk1_4(X17,X18,X19,X20),X20)
        | X20 = k1_enumset1(X17,X18,X19) )
      & ( esk1_4(X17,X18,X19,X20) != X18
        | ~ r2_hidden(esk1_4(X17,X18,X19,X20),X20)
        | X20 = k1_enumset1(X17,X18,X19) )
      & ( esk1_4(X17,X18,X19,X20) != X19
        | ~ r2_hidden(esk1_4(X17,X18,X19,X20),X20)
        | X20 = k1_enumset1(X17,X18,X19) )
      & ( r2_hidden(esk1_4(X17,X18,X19,X20),X20)
        | esk1_4(X17,X18,X19,X20) = X17
        | esk1_4(X17,X18,X19,X20) = X18
        | esk1_4(X17,X18,X19,X20) = X19
        | X20 = k1_enumset1(X17,X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_48,negated_conjecture,
    ( k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = k2_mcart_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,plain,
    ( k4_tarski(X1,X2) != X2 ),
    inference(rw,[status(thm)],[c_0_43,c_0_41])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_54,negated_conjecture,
    ( k4_tarski(k4_tarski(k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)),k2_mcart_1(esk6_0)) = esk6_0 ),
    inference(rw,[status(thm)],[c_0_42,c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( esk6_0 = k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)
    | esk6_0 = k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)
    | esk6_0 = k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_56,negated_conjecture,
    ( k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) != esk6_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_42])).

cnf(c_0_57,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_52])])).

fof(c_0_60,plain,(
    ! [X6] : k3_xboole_0(X6,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_61,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(X8,X9)) = k3_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_62,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk2_1(X2) != k3_mcart_1(X3,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_63,negated_conjecture,
    ( k4_tarski(k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)) = k1_mcart_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_64,negated_conjecture,
    ( k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = esk6_0
    | k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = esk6_0 ),
    inference(sr,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_65,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k1_enumset1(X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_66,plain,
    ( r2_hidden(esk2_1(k1_enumset1(X1,X2,X3)),k1_enumset1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

fof(c_0_67,plain,(
    ! [X28,X29] :
      ( ( k4_xboole_0(X28,k1_tarski(X29)) != X28
        | ~ r2_hidden(X29,X28) )
      & ( r2_hidden(X29,X28)
        | k4_xboole_0(X28,k1_tarski(X29)) = X28 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

cnf(c_0_68,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

fof(c_0_70,plain,(
    ! [X7] : k4_xboole_0(X7,k1_xboole_0) = X7 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_71,plain,
    ( X2 = k1_xboole_0
    | esk2_1(X2) != k4_tarski(k4_tarski(X3,X1),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_62,c_0_25])).

cnf(c_0_72,negated_conjecture,
    ( k4_tarski(k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),esk6_0) = k1_mcart_1(esk6_0)
    | k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_73,plain,
    ( esk2_1(k1_enumset1(X1,X2,X3)) = X3
    | esk2_1(k1_enumset1(X1,X2,X3)) = X2
    | esk2_1(k1_enumset1(X1,X2,X3)) = X1 ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_74,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_75,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_76,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X2,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_78,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk2_1(X2) != k3_mcart_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_79,negated_conjecture,
    ( k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = esk6_0
    | X1 = k1_xboole_0
    | esk2_1(X1) != k4_tarski(k1_mcart_1(esk6_0),X2)
    | ~ r2_hidden(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_80,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk6_0),k2_mcart_1(esk6_0)) = esk6_0 ),
    inference(rw,[status(thm)],[c_0_54,c_0_63])).

cnf(c_0_81,plain,
    ( esk2_1(k1_enumset1(X1,X2,X2)) = X1
    | esk2_1(k1_enumset1(X1,X2,X2)) = X2 ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_73])])).

cnf(c_0_82,plain,
    ( k4_xboole_0(X1,k1_enumset1(X2,X2,X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_30]),c_0_31])).

cnf(c_0_83,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_84,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X1,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_77])])).

cnf(c_0_85,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_86,plain,
    ( X2 = k1_xboole_0
    | esk2_1(X2) != k4_tarski(k4_tarski(X1,X3),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_78,c_0_25])).

cnf(c_0_87,negated_conjecture,
    ( k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = esk6_0
    | X1 = k1_xboole_0
    | esk2_1(X1) != esk6_0
    | ~ r2_hidden(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_88,plain,
    ( esk2_1(k1_enumset1(X1,X1,X1)) = X1 ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_81])])).

cnf(c_0_89,plain,
    ( k1_enumset1(X1,X1,X1) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84])])).

cnf(c_0_90,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_85])])).

cnf(c_0_91,negated_conjecture,
    ( X1 = k1_xboole_0
    | esk2_1(X1) != esk6_0
    | ~ r2_hidden(k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_54])).

cnf(c_0_92,negated_conjecture,
    ( k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89])]),c_0_90])])).

cnf(c_0_93,negated_conjecture,
    ( X1 = k1_xboole_0
    | esk2_1(X1) != esk6_0
    | ~ r2_hidden(esk6_0,X1) ),
    inference(rw,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_94,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_88]),c_0_89])]),c_0_90])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:12:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.54  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.19/0.54  # and selection function SelectNegativeLiterals.
% 0.19/0.54  #
% 0.19/0.54  # Preprocessing time       : 0.027 s
% 0.19/0.54  # Presaturation interreduction done
% 0.19/0.54  
% 0.19/0.54  # Proof found!
% 0.19/0.54  # SZS status Theorem
% 0.19/0.54  # SZS output start CNFRefutation
% 0.19/0.54  fof(t51_mcart_1, conjecture, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_mcart_1)).
% 0.19/0.54  fof(t48_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 0.19/0.54  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.19/0.54  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.19/0.54  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.19/0.54  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.54  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.54  fof(t20_mcart_1, axiom, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.19/0.54  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.19/0.54  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.19/0.54  fof(t29_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k3_mcart_1(X3,X4,X5))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 0.19/0.54  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.19/0.54  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.19/0.54  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.54  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.19/0.54  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.19/0.54  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4))))))), inference(assume_negation,[status(cth)],[t51_mcart_1])).
% 0.19/0.54  fof(c_0_17, plain, ![X44, X45, X46, X47]:(X44=k1_xboole_0|X45=k1_xboole_0|X46=k1_xboole_0|(~m1_subset_1(X47,k3_zfmisc_1(X44,X45,X46))|X47=k3_mcart_1(k5_mcart_1(X44,X45,X46,X47),k6_mcart_1(X44,X45,X46,X47),k7_mcart_1(X44,X45,X46,X47)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).
% 0.19/0.54  fof(c_0_18, plain, ![X30, X31, X32]:k3_mcart_1(X30,X31,X32)=k4_tarski(k4_tarski(X30,X31),X32), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.19/0.54  fof(c_0_19, plain, ![X33, X34, X35]:k3_zfmisc_1(X33,X34,X35)=k2_zfmisc_1(k2_zfmisc_1(X33,X34),X35), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.19/0.54  fof(c_0_20, negated_conjecture, (((esk3_0!=k1_xboole_0&esk4_0!=k1_xboole_0)&esk5_0!=k1_xboole_0)&(m1_subset_1(esk6_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0))&(esk6_0=k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)|esk6_0=k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)|esk6_0=k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.19/0.54  fof(c_0_21, plain, ![X25, X26, X27]:(((r2_hidden(X25,X26)|~r2_hidden(X25,k4_xboole_0(X26,k1_tarski(X27))))&(X25!=X27|~r2_hidden(X25,k4_xboole_0(X26,k1_tarski(X27)))))&(~r2_hidden(X25,X26)|X25=X27|r2_hidden(X25,k4_xboole_0(X26,k1_tarski(X27))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.19/0.54  fof(c_0_22, plain, ![X22]:k2_tarski(X22,X22)=k1_tarski(X22), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.54  fof(c_0_23, plain, ![X23, X24]:k1_enumset1(X23,X23,X24)=k2_tarski(X23,X24), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.54  cnf(c_0_24, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.54  cnf(c_0_25, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.54  cnf(c_0_26, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.54  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk6_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.54  fof(c_0_28, plain, ![X36, X37, X38]:((X36!=k1_mcart_1(X36)|X36!=k4_tarski(X37,X38))&(X36!=k2_mcart_1(X36)|X36!=k4_tarski(X37,X38))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).
% 0.19/0.54  cnf(c_0_29, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.54  cnf(c_0_30, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.54  cnf(c_0_31, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.54  fof(c_0_32, plain, ![X48, X49]:(k1_mcart_1(k4_tarski(X48,X49))=X48&k2_mcart_1(k4_tarski(X48,X49))=X49), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.19/0.54  cnf(c_0_33, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X4=k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.19/0.54  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk6_0,k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0))), inference(rw,[status(thm)],[c_0_27, c_0_26])).
% 0.19/0.54  cnf(c_0_35, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.54  cnf(c_0_36, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.54  cnf(c_0_37, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.54  cnf(c_0_38, plain, (X1!=k2_mcart_1(X1)|X1!=k4_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.54  cnf(c_0_39, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_enumset1(X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.19/0.54  fof(c_0_40, plain, ![X10]:k4_xboole_0(k1_xboole_0,X10)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.19/0.54  cnf(c_0_41, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.54  cnf(c_0_42, negated_conjecture, (k4_tarski(k4_tarski(k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)),k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0))=esk6_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36]), c_0_37])).
% 0.19/0.54  cnf(c_0_43, plain, (k2_mcart_1(k4_tarski(X1,X2))!=k4_tarski(X1,X2)), inference(er,[status(thm)],[c_0_38])).
% 0.19/0.54  cnf(c_0_44, plain, (~r2_hidden(X1,k4_xboole_0(X2,k1_enumset1(X1,X1,X1)))), inference(er,[status(thm)],[c_0_39])).
% 0.19/0.54  cnf(c_0_45, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.54  fof(c_0_46, plain, ![X39, X41, X42, X43]:((r2_hidden(esk2_1(X39),X39)|X39=k1_xboole_0)&((~r2_hidden(X41,X39)|esk2_1(X39)!=k3_mcart_1(X41,X42,X43)|X39=k1_xboole_0)&(~r2_hidden(X42,X39)|esk2_1(X39)!=k3_mcart_1(X41,X42,X43)|X39=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).
% 0.19/0.54  fof(c_0_47, plain, ![X11, X12, X13, X14, X15, X16, X17, X18, X19, X20]:(((~r2_hidden(X15,X14)|(X15=X11|X15=X12|X15=X13)|X14!=k1_enumset1(X11,X12,X13))&(((X16!=X11|r2_hidden(X16,X14)|X14!=k1_enumset1(X11,X12,X13))&(X16!=X12|r2_hidden(X16,X14)|X14!=k1_enumset1(X11,X12,X13)))&(X16!=X13|r2_hidden(X16,X14)|X14!=k1_enumset1(X11,X12,X13))))&((((esk1_4(X17,X18,X19,X20)!=X17|~r2_hidden(esk1_4(X17,X18,X19,X20),X20)|X20=k1_enumset1(X17,X18,X19))&(esk1_4(X17,X18,X19,X20)!=X18|~r2_hidden(esk1_4(X17,X18,X19,X20),X20)|X20=k1_enumset1(X17,X18,X19)))&(esk1_4(X17,X18,X19,X20)!=X19|~r2_hidden(esk1_4(X17,X18,X19,X20),X20)|X20=k1_enumset1(X17,X18,X19)))&(r2_hidden(esk1_4(X17,X18,X19,X20),X20)|(esk1_4(X17,X18,X19,X20)=X17|esk1_4(X17,X18,X19,X20)=X18|esk1_4(X17,X18,X19,X20)=X19)|X20=k1_enumset1(X17,X18,X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.19/0.54  cnf(c_0_48, negated_conjecture, (k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=k2_mcart_1(esk6_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.54  cnf(c_0_49, plain, (k4_tarski(X1,X2)!=X2), inference(rw,[status(thm)],[c_0_43, c_0_41])).
% 0.19/0.54  cnf(c_0_50, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.54  cnf(c_0_51, plain, (r2_hidden(esk2_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.54  cnf(c_0_52, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.54  cnf(c_0_53, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.54  cnf(c_0_54, negated_conjecture, (k4_tarski(k4_tarski(k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)),k2_mcart_1(esk6_0))=esk6_0), inference(rw,[status(thm)],[c_0_42, c_0_48])).
% 0.19/0.54  cnf(c_0_55, negated_conjecture, (esk6_0=k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)|esk6_0=k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)|esk6_0=k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.54  cnf(c_0_56, negated_conjecture, (k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)!=esk6_0), inference(spm,[status(thm)],[c_0_49, c_0_42])).
% 0.19/0.54  cnf(c_0_57, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.54  cnf(c_0_58, plain, (r2_hidden(esk2_1(X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.54  cnf(c_0_59, plain, (r2_hidden(X1,k1_enumset1(X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_52])])).
% 0.19/0.54  fof(c_0_60, plain, ![X6]:k3_xboole_0(X6,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.19/0.54  fof(c_0_61, plain, ![X8, X9]:k4_xboole_0(X8,k4_xboole_0(X8,X9))=k3_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.54  cnf(c_0_62, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk2_1(X2)!=k3_mcart_1(X3,X1,X4)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.54  cnf(c_0_63, negated_conjecture, (k4_tarski(k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0))=k1_mcart_1(esk6_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.54  cnf(c_0_64, negated_conjecture, (k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=esk6_0|k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=esk6_0), inference(sr,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.54  cnf(c_0_65, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k1_enumset1(X4,X3,X2))), inference(er,[status(thm)],[c_0_57])).
% 0.19/0.54  cnf(c_0_66, plain, (r2_hidden(esk2_1(k1_enumset1(X1,X2,X3)),k1_enumset1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.54  fof(c_0_67, plain, ![X28, X29]:((k4_xboole_0(X28,k1_tarski(X29))!=X28|~r2_hidden(X29,X28))&(r2_hidden(X29,X28)|k4_xboole_0(X28,k1_tarski(X29))=X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.19/0.54  cnf(c_0_68, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.54  cnf(c_0_69, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.54  fof(c_0_70, plain, ![X7]:k4_xboole_0(X7,k1_xboole_0)=X7, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.19/0.54  cnf(c_0_71, plain, (X2=k1_xboole_0|esk2_1(X2)!=k4_tarski(k4_tarski(X3,X1),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_62, c_0_25])).
% 0.19/0.54  cnf(c_0_72, negated_conjecture, (k4_tarski(k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),esk6_0)=k1_mcart_1(esk6_0)|k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=esk6_0), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.19/0.54  cnf(c_0_73, plain, (esk2_1(k1_enumset1(X1,X2,X3))=X3|esk2_1(k1_enumset1(X1,X2,X3))=X2|esk2_1(k1_enumset1(X1,X2,X3))=X1), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.54  cnf(c_0_74, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.54  cnf(c_0_75, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 0.19/0.54  cnf(c_0_76, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.19/0.54  cnf(c_0_77, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X2,X5)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.54  cnf(c_0_78, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk2_1(X2)!=k3_mcart_1(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.54  cnf(c_0_79, negated_conjecture, (k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=esk6_0|X1=k1_xboole_0|esk2_1(X1)!=k4_tarski(k1_mcart_1(esk6_0),X2)|~r2_hidden(esk6_0,X1)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.19/0.54  cnf(c_0_80, negated_conjecture, (k4_tarski(k1_mcart_1(esk6_0),k2_mcart_1(esk6_0))=esk6_0), inference(rw,[status(thm)],[c_0_54, c_0_63])).
% 0.19/0.54  cnf(c_0_81, plain, (esk2_1(k1_enumset1(X1,X2,X2))=X1|esk2_1(k1_enumset1(X1,X2,X2))=X2), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_73])])).
% 0.19/0.54  cnf(c_0_82, plain, (k4_xboole_0(X1,k1_enumset1(X2,X2,X2))!=X1|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_30]), c_0_31])).
% 0.19/0.54  cnf(c_0_83, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_75, c_0_76])).
% 0.19/0.54  cnf(c_0_84, plain, (r2_hidden(X1,k1_enumset1(X2,X1,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_77])])).
% 0.19/0.54  cnf(c_0_85, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.54  cnf(c_0_86, plain, (X2=k1_xboole_0|esk2_1(X2)!=k4_tarski(k4_tarski(X1,X3),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_78, c_0_25])).
% 0.19/0.54  cnf(c_0_87, negated_conjecture, (k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=esk6_0|X1=k1_xboole_0|esk2_1(X1)!=esk6_0|~r2_hidden(esk6_0,X1)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.19/0.54  cnf(c_0_88, plain, (esk2_1(k1_enumset1(X1,X1,X1))=X1), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_81])])).
% 0.19/0.54  cnf(c_0_89, plain, (k1_enumset1(X1,X1,X1)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84])])).
% 0.19/0.54  cnf(c_0_90, plain, (r2_hidden(X1,k1_enumset1(X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_85])])).
% 0.19/0.54  cnf(c_0_91, negated_conjecture, (X1=k1_xboole_0|esk2_1(X1)!=esk6_0|~r2_hidden(k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_86, c_0_54])).
% 0.19/0.54  cnf(c_0_92, negated_conjecture, (k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89])]), c_0_90])])).
% 0.19/0.54  cnf(c_0_93, negated_conjecture, (X1=k1_xboole_0|esk2_1(X1)!=esk6_0|~r2_hidden(esk6_0,X1)), inference(rw,[status(thm)],[c_0_91, c_0_92])).
% 0.19/0.54  cnf(c_0_94, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_88]), c_0_89])]), c_0_90])]), ['proof']).
% 0.19/0.54  # SZS output end CNFRefutation
% 0.19/0.54  # Proof object total steps             : 95
% 0.19/0.54  # Proof object clause steps            : 62
% 0.19/0.54  # Proof object formula steps           : 33
% 0.19/0.54  # Proof object conjectures             : 23
% 0.19/0.54  # Proof object clause conjectures      : 20
% 0.19/0.54  # Proof object formula conjectures     : 3
% 0.19/0.54  # Proof object initial clauses used    : 26
% 0.19/0.54  # Proof object initial formulas used   : 16
% 0.19/0.54  # Proof object generating inferences   : 17
% 0.19/0.54  # Proof object simplifying inferences  : 40
% 0.19/0.54  # Training examples: 0 positive, 0 negative
% 0.19/0.54  # Parsed axioms                        : 16
% 0.19/0.54  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.54  # Initial clauses                      : 34
% 0.19/0.54  # Removed in clause preprocessing      : 5
% 0.19/0.54  # Initial clauses in saturation        : 29
% 0.19/0.54  # Processed clauses                    : 1155
% 0.19/0.54  # ...of these trivial                  : 14
% 0.19/0.54  # ...subsumed                          : 778
% 0.19/0.54  # ...remaining for further processing  : 363
% 0.19/0.54  # Other redundant clauses eliminated   : 2197
% 0.19/0.54  # Clauses deleted for lack of memory   : 0
% 0.19/0.54  # Backward-subsumed                    : 7
% 0.19/0.54  # Backward-rewritten                   : 35
% 0.19/0.54  # Generated clauses                    : 17322
% 0.19/0.54  # ...of the previous two non-trivial   : 13817
% 0.19/0.54  # Contextual simplify-reflections      : 2
% 0.19/0.54  # Paramodulations                      : 15093
% 0.19/0.54  # Factorizations                       : 34
% 0.19/0.54  # Equation resolutions                 : 2197
% 0.19/0.54  # Propositional unsat checks           : 0
% 0.19/0.54  #    Propositional check models        : 0
% 0.19/0.54  #    Propositional check unsatisfiable : 0
% 0.19/0.54  #    Propositional clauses             : 0
% 0.19/0.54  #    Propositional clauses after purity: 0
% 0.19/0.54  #    Propositional unsat core size     : 0
% 0.19/0.54  #    Propositional preprocessing time  : 0.000
% 0.19/0.54  #    Propositional encoding time       : 0.000
% 0.19/0.54  #    Propositional solver time         : 0.000
% 0.19/0.54  #    Success case prop preproc time    : 0.000
% 0.19/0.54  #    Success case prop encoding time   : 0.000
% 0.19/0.54  #    Success case prop solver time     : 0.000
% 0.19/0.54  # Current number of processed clauses  : 284
% 0.19/0.54  #    Positive orientable unit clauses  : 23
% 0.19/0.54  #    Positive unorientable unit clauses: 0
% 0.19/0.54  #    Negative unit clauses             : 11
% 0.19/0.54  #    Non-unit-clauses                  : 250
% 0.19/0.54  # Current number of unprocessed clauses: 12645
% 0.19/0.54  # ...number of literals in the above   : 44679
% 0.19/0.54  # Current number of archived formulas  : 0
% 0.19/0.54  # Current number of archived clauses   : 77
% 0.19/0.54  # Clause-clause subsumption calls (NU) : 7993
% 0.19/0.54  # Rec. Clause-clause subsumption calls : 5438
% 0.19/0.54  # Non-unit clause-clause subsumptions  : 502
% 0.19/0.54  # Unit Clause-clause subsumption calls : 463
% 0.19/0.54  # Rewrite failures with RHS unbound    : 0
% 0.19/0.54  # BW rewrite match attempts            : 31
% 0.19/0.54  # BW rewrite match successes           : 6
% 0.19/0.54  # Condensation attempts                : 0
% 0.19/0.54  # Condensation successes               : 0
% 0.19/0.54  # Termbank termtop insertions          : 276507
% 0.19/0.54  
% 0.19/0.54  # -------------------------------------------------
% 0.19/0.54  # User time                : 0.183 s
% 0.19/0.54  # System time              : 0.013 s
% 0.19/0.54  # Total time               : 0.196 s
% 0.19/0.54  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
