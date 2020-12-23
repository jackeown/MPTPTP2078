%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:28 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 (2338 expanded)
%              Number of clauses        :   45 (1071 expanded)
%              Number of leaves         :    9 ( 612 expanded)
%              Depth                    :   21
%              Number of atoms          :  176 (5839 expanded)
%              Number of equality atoms :   79 (3052 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t113_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(c_0_9,plain,(
    ! [X38,X39,X40] :
      ( ( r2_hidden(X38,X39)
        | ~ r2_hidden(X38,k4_xboole_0(X39,k1_tarski(X40))) )
      & ( X38 != X40
        | ~ r2_hidden(X38,k4_xboole_0(X39,k1_tarski(X40))) )
      & ( ~ r2_hidden(X38,X39)
        | X38 = X40
        | r2_hidden(X38,k4_xboole_0(X39,k1_tarski(X40))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_10,plain,(
    ! [X11] : k2_tarski(X11,X11) = k1_tarski(X11) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_11,plain,(
    ! [X12,X13] : k1_enumset1(X12,X12,X13) = k2_tarski(X12,X13) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X14,X15,X16] : k2_enumset1(X14,X14,X15,X16) = k1_enumset1(X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_13,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X7,X8] :
      ( ( k4_xboole_0(X7,X8) != k1_xboole_0
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | k4_xboole_0(X7,X8) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_18,plain,(
    ! [X9,X10] : r1_tarski(k4_xboole_0(X9,X10),X9) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k1_xboole_0
      <=> ( X1 = k1_xboole_0
          | X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t113_zfmisc_1])).

cnf(c_0_20,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k2_enumset1(X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,negated_conjecture,
    ( ( esk6_0 != k1_xboole_0
      | k2_zfmisc_1(esk6_0,esk7_0) != k1_xboole_0 )
    & ( esk7_0 != k1_xboole_0
      | k2_zfmisc_1(esk6_0,esk7_0) != k1_xboole_0 )
    & ( k2_zfmisc_1(esk6_0,esk7_0) = k1_xboole_0
      | esk6_0 = k1_xboole_0
      | esk7_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])])).

fof(c_0_24,plain,(
    ! [X17,X18,X19,X20,X23,X24,X25,X26,X27,X28,X30,X31] :
      ( ( r2_hidden(esk1_4(X17,X18,X19,X20),X17)
        | ~ r2_hidden(X20,X19)
        | X19 != k2_zfmisc_1(X17,X18) )
      & ( r2_hidden(esk2_4(X17,X18,X19,X20),X18)
        | ~ r2_hidden(X20,X19)
        | X19 != k2_zfmisc_1(X17,X18) )
      & ( X20 = k4_tarski(esk1_4(X17,X18,X19,X20),esk2_4(X17,X18,X19,X20))
        | ~ r2_hidden(X20,X19)
        | X19 != k2_zfmisc_1(X17,X18) )
      & ( ~ r2_hidden(X24,X17)
        | ~ r2_hidden(X25,X18)
        | X23 != k4_tarski(X24,X25)
        | r2_hidden(X23,X19)
        | X19 != k2_zfmisc_1(X17,X18) )
      & ( ~ r2_hidden(esk3_3(X26,X27,X28),X28)
        | ~ r2_hidden(X30,X26)
        | ~ r2_hidden(X31,X27)
        | esk3_3(X26,X27,X28) != k4_tarski(X30,X31)
        | X28 = k2_zfmisc_1(X26,X27) )
      & ( r2_hidden(esk4_3(X26,X27,X28),X26)
        | r2_hidden(esk3_3(X26,X27,X28),X28)
        | X28 = k2_zfmisc_1(X26,X27) )
      & ( r2_hidden(esk5_3(X26,X27,X28),X27)
        | r2_hidden(esk3_3(X26,X27,X28),X28)
        | X28 = k2_zfmisc_1(X26,X27) )
      & ( esk3_3(X26,X27,X28) = k4_tarski(esk4_3(X26,X27,X28),esk5_3(X26,X27,X28))
        | r2_hidden(esk3_3(X26,X27,X28),X28)
        | X28 = k2_zfmisc_1(X26,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( k2_zfmisc_1(esk6_0,esk7_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X1)
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | k2_zfmisc_1(esk6_0,esk7_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | r2_hidden(esk4_3(esk6_0,esk7_0,X1),esk6_0)
    | r2_hidden(esk3_3(esk6_0,esk7_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | k2_zfmisc_1(esk6_0,esk7_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk5_3(esk6_0,esk7_0,k1_xboole_0),esk7_0)
    | esk7_0 != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30])]),c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | r2_hidden(esk3_3(esk6_0,esk7_0,esk7_0),esk7_0)
    | r2_hidden(esk4_3(esk6_0,esk7_0,esk7_0),esk6_0) ),
    inference(ef,[status(thm)],[c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | r2_hidden(esk5_3(esk6_0,esk7_0,X1),esk7_0)
    | r2_hidden(esk3_3(esk6_0,esk7_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_30])).

fof(c_0_37,plain,(
    ! [X34,X35,X36,X37] :
      ( ( r2_hidden(X34,X36)
        | ~ r2_hidden(k4_tarski(X34,X35),k2_zfmisc_1(X36,X37)) )
      & ( r2_hidden(X35,X37)
        | ~ r2_hidden(k4_tarski(X34,X35),k2_zfmisc_1(X36,X37)) )
      & ( ~ r2_hidden(X34,X36)
        | ~ r2_hidden(X35,X37)
        | r2_hidden(k4_tarski(X34,X35),k2_zfmisc_1(X36,X37)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk4_3(esk6_0,esk7_0,k1_xboole_0),esk6_0)
    | esk6_0 != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_28])]),c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk4_3(esk6_0,esk7_0,esk7_0),esk6_0)
    | r2_hidden(esk3_3(esk6_0,esk7_0,esk7_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | r2_hidden(esk3_3(esk6_0,esk7_0,esk7_0),esk7_0)
    | r2_hidden(esk5_3(esk6_0,esk7_0,esk7_0),esk7_0) ),
    inference(ef,[status(thm)],[c_0_36])).

cnf(c_0_41,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk3_3(esk6_0,esk7_0,esk7_0),esk7_0)
    | r2_hidden(esk4_3(esk6_0,esk7_0,esk7_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_31])).

cnf(c_0_43,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk5_3(esk6_0,esk7_0,esk7_0),esk7_0)
    | r2_hidden(esk3_3(esk6_0,esk7_0,esk7_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_40]),c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_3(esk6_0,esk7_0,esk7_0),X1),k2_zfmisc_1(esk6_0,X2))
    | r2_hidden(esk3_3(esk6_0,esk7_0,esk7_0),esk7_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk3_3(esk6_0,esk7_0,esk7_0),esk7_0)
    | r2_hidden(esk5_3(esk6_0,esk7_0,esk7_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_43]),c_0_31])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_3(esk6_0,esk7_0,esk7_0),esk5_3(esk6_0,esk7_0,esk7_0)),k2_zfmisc_1(esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk6_0,esk7_0,esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_47,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | r2_hidden(esk3_3(esk6_0,esk7_0,esk7_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_27]),c_0_31])).

cnf(c_0_48,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk3_3(esk6_0,esk7_0,esk7_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_47]),c_0_31])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk3_3(esk6_0,esk7_0,esk7_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_48]),c_0_31])).

cnf(c_0_50,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_26])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_3(esk6_0,esk7_0,esk7_0),X1),k2_zfmisc_1(esk7_0,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_49])).

cnf(c_0_52,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_3(esk6_0,esk7_0,esk7_0),esk3_3(esk6_0,esk7_0,esk7_0)),k2_zfmisc_1(esk7_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_49])).

cnf(c_0_54,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | r2_hidden(esk5_3(X1,X2,k1_xboole_0),X2) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_30]),c_0_52]),c_0_52]),c_0_52]),c_0_31])).

cnf(c_0_55,plain,
    ( X1 = X2
    | r2_hidden(esk4_3(X3,X4,X2),X3)
    | r2_hidden(esk3_3(X3,X4,X2),X2)
    | r2_hidden(esk4_3(X3,X4,X1),X3)
    | r2_hidden(esk3_3(X3,X4,X1),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_28])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk5_3(esk7_0,esk7_0,k1_xboole_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_31])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk3_3(X1,X2,esk6_0),esk6_0)
    | r2_hidden(esk4_3(X1,X2,k1_xboole_0),X1)
    | r2_hidden(esk4_3(X1,X2,esk6_0),X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_55])]),c_0_31]),c_0_31])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk5_3(esk7_0,esk7_0,k1_xboole_0)),k2_zfmisc_1(X2,esk7_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk3_3(k1_xboole_0,X1,esk6_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_57]),c_0_31])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_3(k1_xboole_0,X1,esk6_0),esk5_3(esk7_0,esk7_0,k1_xboole_0)),k2_zfmisc_1(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_61,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_27]),c_0_31])).

cnf(c_0_62,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_61]),c_0_31])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_62]),c_0_62]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:50:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.50  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.21/0.50  # and selection function SelectNegativeLiterals.
% 0.21/0.50  #
% 0.21/0.50  # Preprocessing time       : 0.030 s
% 0.21/0.50  # Presaturation interreduction done
% 0.21/0.50  
% 0.21/0.50  # Proof found!
% 0.21/0.50  # SZS status Theorem
% 0.21/0.50  # SZS output start CNFRefutation
% 0.21/0.50  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.21/0.50  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.50  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.50  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.50  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.21/0.50  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.21/0.50  fof(t113_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.21/0.50  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.21/0.50  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.21/0.50  fof(c_0_9, plain, ![X38, X39, X40]:(((r2_hidden(X38,X39)|~r2_hidden(X38,k4_xboole_0(X39,k1_tarski(X40))))&(X38!=X40|~r2_hidden(X38,k4_xboole_0(X39,k1_tarski(X40)))))&(~r2_hidden(X38,X39)|X38=X40|r2_hidden(X38,k4_xboole_0(X39,k1_tarski(X40))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.21/0.50  fof(c_0_10, plain, ![X11]:k2_tarski(X11,X11)=k1_tarski(X11), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.50  fof(c_0_11, plain, ![X12, X13]:k1_enumset1(X12,X12,X13)=k2_tarski(X12,X13), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.50  fof(c_0_12, plain, ![X14, X15, X16]:k2_enumset1(X14,X14,X15,X16)=k1_enumset1(X14,X15,X16), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.50  cnf(c_0_13, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.50  cnf(c_0_14, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.50  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.50  cnf(c_0_16, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.50  fof(c_0_17, plain, ![X7, X8]:((k4_xboole_0(X7,X8)!=k1_xboole_0|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|k4_xboole_0(X7,X8)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.21/0.50  fof(c_0_18, plain, ![X9, X10]:r1_tarski(k4_xboole_0(X9,X10),X9), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.21/0.50  fof(c_0_19, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t113_zfmisc_1])).
% 0.21/0.50  cnf(c_0_20, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k2_enumset1(X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16])).
% 0.21/0.50  cnf(c_0_21, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.50  cnf(c_0_22, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.50  fof(c_0_23, negated_conjecture, (((esk6_0!=k1_xboole_0|k2_zfmisc_1(esk6_0,esk7_0)!=k1_xboole_0)&(esk7_0!=k1_xboole_0|k2_zfmisc_1(esk6_0,esk7_0)!=k1_xboole_0))&(k2_zfmisc_1(esk6_0,esk7_0)=k1_xboole_0|(esk6_0=k1_xboole_0|esk7_0=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])])).
% 0.21/0.50  fof(c_0_24, plain, ![X17, X18, X19, X20, X23, X24, X25, X26, X27, X28, X30, X31]:(((((r2_hidden(esk1_4(X17,X18,X19,X20),X17)|~r2_hidden(X20,X19)|X19!=k2_zfmisc_1(X17,X18))&(r2_hidden(esk2_4(X17,X18,X19,X20),X18)|~r2_hidden(X20,X19)|X19!=k2_zfmisc_1(X17,X18)))&(X20=k4_tarski(esk1_4(X17,X18,X19,X20),esk2_4(X17,X18,X19,X20))|~r2_hidden(X20,X19)|X19!=k2_zfmisc_1(X17,X18)))&(~r2_hidden(X24,X17)|~r2_hidden(X25,X18)|X23!=k4_tarski(X24,X25)|r2_hidden(X23,X19)|X19!=k2_zfmisc_1(X17,X18)))&((~r2_hidden(esk3_3(X26,X27,X28),X28)|(~r2_hidden(X30,X26)|~r2_hidden(X31,X27)|esk3_3(X26,X27,X28)!=k4_tarski(X30,X31))|X28=k2_zfmisc_1(X26,X27))&(((r2_hidden(esk4_3(X26,X27,X28),X26)|r2_hidden(esk3_3(X26,X27,X28),X28)|X28=k2_zfmisc_1(X26,X27))&(r2_hidden(esk5_3(X26,X27,X28),X27)|r2_hidden(esk3_3(X26,X27,X28),X28)|X28=k2_zfmisc_1(X26,X27)))&(esk3_3(X26,X27,X28)=k4_tarski(esk4_3(X26,X27,X28),esk5_3(X26,X27,X28))|r2_hidden(esk3_3(X26,X27,X28),X28)|X28=k2_zfmisc_1(X26,X27))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.21/0.50  cnf(c_0_25, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)))), inference(er,[status(thm)],[c_0_20])).
% 0.21/0.50  cnf(c_0_26, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.21/0.50  cnf(c_0_27, negated_conjecture, (k2_zfmisc_1(esk6_0,esk7_0)=k1_xboole_0|esk6_0=k1_xboole_0|esk7_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.50  cnf(c_0_28, plain, (r2_hidden(esk4_3(X1,X2,X3),X1)|r2_hidden(esk3_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.50  cnf(c_0_29, negated_conjecture, (esk7_0!=k1_xboole_0|k2_zfmisc_1(esk6_0,esk7_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.50  cnf(c_0_30, plain, (r2_hidden(esk5_3(X1,X2,X3),X2)|r2_hidden(esk3_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.50  cnf(c_0_31, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.21/0.50  cnf(c_0_32, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|X1=k1_xboole_0|r2_hidden(esk4_3(esk6_0,esk7_0,X1),esk6_0)|r2_hidden(esk3_3(esk6_0,esk7_0,X1),X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.50  cnf(c_0_33, negated_conjecture, (esk6_0!=k1_xboole_0|k2_zfmisc_1(esk6_0,esk7_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.50  cnf(c_0_34, negated_conjecture, (r2_hidden(esk5_3(esk6_0,esk7_0,k1_xboole_0),esk7_0)|esk7_0!=k1_xboole_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30])]), c_0_31])).
% 0.21/0.50  cnf(c_0_35, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|r2_hidden(esk3_3(esk6_0,esk7_0,esk7_0),esk7_0)|r2_hidden(esk4_3(esk6_0,esk7_0,esk7_0),esk6_0)), inference(ef,[status(thm)],[c_0_32])).
% 0.21/0.50  cnf(c_0_36, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|X1=k1_xboole_0|r2_hidden(esk5_3(esk6_0,esk7_0,X1),esk7_0)|r2_hidden(esk3_3(esk6_0,esk7_0,X1),X1)), inference(spm,[status(thm)],[c_0_27, c_0_30])).
% 0.21/0.50  fof(c_0_37, plain, ![X34, X35, X36, X37]:(((r2_hidden(X34,X36)|~r2_hidden(k4_tarski(X34,X35),k2_zfmisc_1(X36,X37)))&(r2_hidden(X35,X37)|~r2_hidden(k4_tarski(X34,X35),k2_zfmisc_1(X36,X37))))&(~r2_hidden(X34,X36)|~r2_hidden(X35,X37)|r2_hidden(k4_tarski(X34,X35),k2_zfmisc_1(X36,X37)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.21/0.50  cnf(c_0_38, negated_conjecture, (r2_hidden(esk4_3(esk6_0,esk7_0,k1_xboole_0),esk6_0)|esk6_0!=k1_xboole_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_28])]), c_0_31])).
% 0.21/0.50  cnf(c_0_39, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk4_3(esk6_0,esk7_0,esk7_0),esk6_0)|r2_hidden(esk3_3(esk6_0,esk7_0,esk7_0),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_31])).
% 0.21/0.50  cnf(c_0_40, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|r2_hidden(esk3_3(esk6_0,esk7_0,esk7_0),esk7_0)|r2_hidden(esk5_3(esk6_0,esk7_0,esk7_0),esk7_0)), inference(ef,[status(thm)],[c_0_36])).
% 0.21/0.50  cnf(c_0_41, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.50  cnf(c_0_42, negated_conjecture, (r2_hidden(esk3_3(esk6_0,esk7_0,esk7_0),esk7_0)|r2_hidden(esk4_3(esk6_0,esk7_0,esk7_0),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_31])).
% 0.21/0.50  cnf(c_0_43, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk5_3(esk6_0,esk7_0,esk7_0),esk7_0)|r2_hidden(esk3_3(esk6_0,esk7_0,esk7_0),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_40]), c_0_31])).
% 0.21/0.50  cnf(c_0_44, negated_conjecture, (r2_hidden(k4_tarski(esk4_3(esk6_0,esk7_0,esk7_0),X1),k2_zfmisc_1(esk6_0,X2))|r2_hidden(esk3_3(esk6_0,esk7_0,esk7_0),esk7_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.21/0.50  cnf(c_0_45, negated_conjecture, (r2_hidden(esk3_3(esk6_0,esk7_0,esk7_0),esk7_0)|r2_hidden(esk5_3(esk6_0,esk7_0,esk7_0),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_43]), c_0_31])).
% 0.21/0.50  cnf(c_0_46, negated_conjecture, (r2_hidden(k4_tarski(esk4_3(esk6_0,esk7_0,esk7_0),esk5_3(esk6_0,esk7_0,esk7_0)),k2_zfmisc_1(esk6_0,esk7_0))|r2_hidden(esk3_3(esk6_0,esk7_0,esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.21/0.50  cnf(c_0_47, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|r2_hidden(esk3_3(esk6_0,esk7_0,esk7_0),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_27]), c_0_31])).
% 0.21/0.50  cnf(c_0_48, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk3_3(esk6_0,esk7_0,esk7_0),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_47]), c_0_31])).
% 0.21/0.50  cnf(c_0_49, negated_conjecture, (r2_hidden(esk3_3(esk6_0,esk7_0,esk7_0),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_48]), c_0_31])).
% 0.21/0.50  cnf(c_0_50, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_26, c_0_26])).
% 0.21/0.50  cnf(c_0_51, negated_conjecture, (r2_hidden(k4_tarski(esk3_3(esk6_0,esk7_0,esk7_0),X1),k2_zfmisc_1(esk7_0,X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_41, c_0_49])).
% 0.21/0.50  cnf(c_0_52, plain, (k4_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_26, c_0_50])).
% 0.21/0.50  cnf(c_0_53, negated_conjecture, (r2_hidden(k4_tarski(esk3_3(esk6_0,esk7_0,esk7_0),esk3_3(esk6_0,esk7_0,esk7_0)),k2_zfmisc_1(esk7_0,esk7_0))), inference(spm,[status(thm)],[c_0_51, c_0_49])).
% 0.21/0.50  cnf(c_0_54, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|r2_hidden(esk5_3(X1,X2,k1_xboole_0),X2)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_30]), c_0_52]), c_0_52]), c_0_52]), c_0_31])).
% 0.21/0.50  cnf(c_0_55, plain, (X1=X2|r2_hidden(esk4_3(X3,X4,X2),X3)|r2_hidden(esk3_3(X3,X4,X2),X2)|r2_hidden(esk4_3(X3,X4,X1),X3)|r2_hidden(esk3_3(X3,X4,X1),X1)), inference(spm,[status(thm)],[c_0_28, c_0_28])).
% 0.21/0.50  cnf(c_0_56, negated_conjecture, (r2_hidden(esk5_3(esk7_0,esk7_0,k1_xboole_0),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_31])).
% 0.21/0.50  cnf(c_0_57, negated_conjecture, (r2_hidden(esk3_3(X1,X2,esk6_0),esk6_0)|r2_hidden(esk4_3(X1,X2,k1_xboole_0),X1)|r2_hidden(esk4_3(X1,X2,esk6_0),X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_55])]), c_0_31]), c_0_31])).
% 0.21/0.50  cnf(c_0_58, negated_conjecture, (r2_hidden(k4_tarski(X1,esk5_3(esk7_0,esk7_0,k1_xboole_0)),k2_zfmisc_1(X2,esk7_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_41, c_0_56])).
% 0.21/0.50  cnf(c_0_59, negated_conjecture, (r2_hidden(esk3_3(k1_xboole_0,X1,esk6_0),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_57]), c_0_31])).
% 0.21/0.50  cnf(c_0_60, negated_conjecture, (r2_hidden(k4_tarski(esk3_3(k1_xboole_0,X1,esk6_0),esk5_3(esk7_0,esk7_0,k1_xboole_0)),k2_zfmisc_1(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.21/0.50  cnf(c_0_61, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_27]), c_0_31])).
% 0.21/0.50  cnf(c_0_62, negated_conjecture, (esk6_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_61]), c_0_31])).
% 0.21/0.50  cnf(c_0_63, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_62]), c_0_62]), c_0_31]), ['proof']).
% 0.21/0.50  # SZS output end CNFRefutation
% 0.21/0.50  # Proof object total steps             : 64
% 0.21/0.50  # Proof object clause steps            : 45
% 0.21/0.50  # Proof object formula steps           : 19
% 0.21/0.50  # Proof object conjectures             : 31
% 0.21/0.50  # Proof object clause conjectures      : 28
% 0.21/0.50  # Proof object formula conjectures     : 3
% 0.21/0.50  # Proof object initial clauses used    : 12
% 0.21/0.50  # Proof object initial formulas used   : 9
% 0.21/0.50  # Proof object generating inferences   : 30
% 0.21/0.50  # Proof object simplifying inferences  : 29
% 0.21/0.50  # Training examples: 0 positive, 0 negative
% 0.21/0.50  # Parsed axioms                        : 9
% 0.21/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.50  # Initial clauses                      : 23
% 0.21/0.50  # Removed in clause preprocessing      : 3
% 0.21/0.50  # Initial clauses in saturation        : 20
% 0.21/0.50  # Processed clauses                    : 493
% 0.21/0.50  # ...of these trivial                  : 20
% 0.21/0.50  # ...subsumed                          : 241
% 0.21/0.50  # ...remaining for further processing  : 232
% 0.21/0.50  # Other redundant clauses eliminated   : 242
% 0.21/0.50  # Clauses deleted for lack of memory   : 0
% 0.21/0.50  # Backward-subsumed                    : 24
% 0.21/0.50  # Backward-rewritten                   : 72
% 0.21/0.50  # Generated clauses                    : 9324
% 0.21/0.50  # ...of the previous two non-trivial   : 8276
% 0.21/0.50  # Contextual simplify-reflections      : 0
% 0.21/0.50  # Paramodulations                      : 9069
% 0.21/0.50  # Factorizations                       : 14
% 0.21/0.50  # Equation resolutions                 : 242
% 0.21/0.50  # Propositional unsat checks           : 0
% 0.21/0.50  #    Propositional check models        : 0
% 0.21/0.50  #    Propositional check unsatisfiable : 0
% 0.21/0.50  #    Propositional clauses             : 0
% 0.21/0.50  #    Propositional clauses after purity: 0
% 0.21/0.50  #    Propositional unsat core size     : 0
% 0.21/0.50  #    Propositional preprocessing time  : 0.000
% 0.21/0.50  #    Propositional encoding time       : 0.000
% 0.21/0.50  #    Propositional solver time         : 0.000
% 0.21/0.50  #    Success case prop preproc time    : 0.000
% 0.21/0.50  #    Success case prop encoding time   : 0.000
% 0.21/0.50  #    Success case prop solver time     : 0.000
% 0.21/0.50  # Current number of processed clauses  : 112
% 0.21/0.50  #    Positive orientable unit clauses  : 26
% 0.21/0.50  #    Positive unorientable unit clauses: 0
% 0.21/0.50  #    Negative unit clauses             : 2
% 0.21/0.50  #    Non-unit-clauses                  : 84
% 0.21/0.50  # Current number of unprocessed clauses: 7679
% 0.21/0.50  # ...number of literals in the above   : 31786
% 0.21/0.50  # Current number of archived formulas  : 0
% 0.21/0.50  # Current number of archived clauses   : 118
% 0.21/0.50  # Clause-clause subsumption calls (NU) : 3864
% 0.21/0.50  # Rec. Clause-clause subsumption calls : 1842
% 0.21/0.50  # Non-unit clause-clause subsumptions  : 243
% 0.21/0.50  # Unit Clause-clause subsumption calls : 198
% 0.21/0.50  # Rewrite failures with RHS unbound    : 0
% 0.21/0.50  # BW rewrite match attempts            : 12
% 0.21/0.50  # BW rewrite match successes           : 3
% 0.21/0.50  # Condensation attempts                : 0
% 0.21/0.50  # Condensation successes               : 0
% 0.21/0.50  # Termbank termtop insertions          : 177492
% 0.21/0.50  
% 0.21/0.50  # -------------------------------------------------
% 0.21/0.50  # User time                : 0.147 s
% 0.21/0.50  # System time              : 0.009 s
% 0.21/0.50  # Total time               : 0.156 s
% 0.21/0.50  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
