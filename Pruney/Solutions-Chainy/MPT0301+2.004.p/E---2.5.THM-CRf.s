%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:25 EST 2020

% Result     : Theorem 0.62s
% Output     : CNFRefutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   59 (2518 expanded)
%              Number of clauses        :   44 (1131 expanded)
%              Number of leaves         :    7 ( 665 expanded)
%              Depth                    :   20
%              Number of atoms          :  162 (6408 expanded)
%              Number of equality atoms :   72 (3060 expanded)
%              Maximal formula depth    :   23 (   3 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(l97_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k1_xboole_0
      <=> ( X1 = k1_xboole_0
          | X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t113_zfmisc_1])).

fof(c_0_8,plain,(
    ! [X15,X16] : r1_xboole_0(k3_xboole_0(X15,X16),k5_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[l97_xboole_1])).

fof(c_0_9,plain,(
    ! [X18] : k5_xboole_0(X18,k1_xboole_0) = X18 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_10,plain,(
    ! [X17] : k3_xboole_0(X17,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_11,negated_conjecture,
    ( ( esk7_0 != k1_xboole_0
      | k2_zfmisc_1(esk7_0,esk8_0) != k1_xboole_0 )
    & ( esk8_0 != k1_xboole_0
      | k2_zfmisc_1(esk7_0,esk8_0) != k1_xboole_0 )
    & ( k2_zfmisc_1(esk7_0,esk8_0) = k1_xboole_0
      | esk7_0 = k1_xboole_0
      | esk8_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

fof(c_0_12,plain,(
    ! [X19,X20,X21,X22,X25,X26,X27,X28,X29,X30,X32,X33] :
      ( ( r2_hidden(esk2_4(X19,X20,X21,X22),X19)
        | ~ r2_hidden(X22,X21)
        | X21 != k2_zfmisc_1(X19,X20) )
      & ( r2_hidden(esk3_4(X19,X20,X21,X22),X20)
        | ~ r2_hidden(X22,X21)
        | X21 != k2_zfmisc_1(X19,X20) )
      & ( X22 = k4_tarski(esk2_4(X19,X20,X21,X22),esk3_4(X19,X20,X21,X22))
        | ~ r2_hidden(X22,X21)
        | X21 != k2_zfmisc_1(X19,X20) )
      & ( ~ r2_hidden(X26,X19)
        | ~ r2_hidden(X27,X20)
        | X25 != k4_tarski(X26,X27)
        | r2_hidden(X25,X21)
        | X21 != k2_zfmisc_1(X19,X20) )
      & ( ~ r2_hidden(esk4_3(X28,X29,X30),X30)
        | ~ r2_hidden(X32,X28)
        | ~ r2_hidden(X33,X29)
        | esk4_3(X28,X29,X30) != k4_tarski(X32,X33)
        | X30 = k2_zfmisc_1(X28,X29) )
      & ( r2_hidden(esk5_3(X28,X29,X30),X28)
        | r2_hidden(esk4_3(X28,X29,X30),X30)
        | X30 = k2_zfmisc_1(X28,X29) )
      & ( r2_hidden(esk6_3(X28,X29,X30),X29)
        | r2_hidden(esk4_3(X28,X29,X30),X30)
        | X30 = k2_zfmisc_1(X28,X29) )
      & ( esk4_3(X28,X29,X30) = k4_tarski(esk5_3(X28,X29,X30),esk6_3(X28,X29,X30))
        | r2_hidden(esk4_3(X28,X29,X30),X30)
        | X30 = k2_zfmisc_1(X28,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

fof(c_0_13,plain,(
    ! [X9,X10,X12,X13,X14] :
      ( ( r1_xboole_0(X9,X10)
        | r2_hidden(esk1_2(X9,X10),k3_xboole_0(X9,X10)) )
      & ( ~ r2_hidden(X14,k3_xboole_0(X12,X13))
        | ~ r1_xboole_0(X12,X13) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_14,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( k2_zfmisc_1(esk7_0,esk8_0) = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X1)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | r2_hidden(esk5_3(esk7_0,esk8_0,X1),esk7_0)
    | r2_hidden(esk4_3(esk7_0,esk8_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( esk8_0 != k1_xboole_0
    | k2_zfmisc_1(esk7_0,esk8_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)
    | r2_hidden(esk5_3(esk7_0,esk8_0,esk8_0),esk7_0) ),
    inference(ef,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | k2_zfmisc_1(esk7_0,esk8_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk5_3(esk7_0,esk8_0,esk8_0),esk7_0)
    | r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)
    | k2_zfmisc_1(esk7_0,k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk6_3(esk7_0,esk8_0,k1_xboole_0),esk8_0)
    | esk8_0 != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_25])]),c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | r2_hidden(esk6_3(esk7_0,esk8_0,X1),esk8_0)
    | r2_hidden(esk4_3(esk7_0,esk8_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_25])).

cnf(c_0_31,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk5_3(esk7_0,esk8_0,k1_xboole_0),esk7_0)
    | esk7_0 != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_18])]),c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)
    | r2_hidden(esk5_3(esk7_0,esk8_0,esk8_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_25]),c_0_26])]),c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | r2_hidden(esk6_3(esk7_0,esk8_0,X1),esk8_0)
    | r2_hidden(esk4_3(esk7_0,esk8_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_26])).

cnf(c_0_35,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_31])])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk5_3(esk7_0,esk8_0,esk8_0),esk7_0)
    | r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)
    | r2_hidden(esk6_3(esk7_0,esk8_0,esk8_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_34]),c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_3(esk7_0,esk8_0,esk8_0),X1),k2_zfmisc_1(esk7_0,X2))
    | r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk6_3(esk7_0,esk8_0,esk8_0),esk8_0)
    | r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_37]),c_0_26])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_3(esk7_0,esk8_0,esk8_0),esk6_3(esk7_0,esk8_0,esk8_0)),k2_zfmisc_1(esk7_0,esk8_0))
    | r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_41,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_17]),c_0_26])).

cnf(c_0_42,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_41]),c_0_26])).

cnf(c_0_43,plain,
    ( X1 = X2
    | r2_hidden(esk5_3(X3,X4,X2),X3)
    | r2_hidden(esk4_3(X3,X4,X2),X2)
    | r2_hidden(esk5_3(X3,X4,X1),X3)
    | r2_hidden(esk4_3(X3,X4,X1),X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_18])).

fof(c_0_44,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_42]),c_0_26])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk4_3(X1,X2,esk7_0),esk7_0)
    | r2_hidden(esk5_3(X1,X2,k1_xboole_0),X1)
    | r2_hidden(esk5_3(X1,X2,esk7_0),X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_43])]),c_0_26]),c_0_26])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_3(esk7_0,esk8_0,esk8_0),X1),k2_zfmisc_1(esk8_0,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk4_3(k1_xboole_0,X1,esk7_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_46]),c_0_26])).

cnf(c_0_50,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_3(esk7_0,esk8_0,esk8_0),esk4_3(k1_xboole_0,X1,esk7_0)),k2_zfmisc_1(esk8_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | r2_hidden(esk6_3(X1,X2,k1_xboole_0),X2) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_25]),c_0_50]),c_0_50]),c_0_50]),c_0_26])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk4_3(esk7_0,esk8_0,esk8_0)),k2_zfmisc_1(X2,esk8_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk6_3(esk8_0,esk7_0,k1_xboole_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_26])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_3(esk8_0,esk7_0,k1_xboole_0),esk4_3(esk7_0,esk8_0,esk8_0)),k2_zfmisc_1(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_56,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_17]),c_0_26])).

cnf(c_0_57,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_56]),c_0_26])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_57]),c_0_57]),c_0_26]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:18:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.62/0.80  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.62/0.80  # and selection function SelectNegativeLiterals.
% 0.62/0.80  #
% 0.62/0.80  # Preprocessing time       : 0.027 s
% 0.62/0.80  # Presaturation interreduction done
% 0.62/0.80  
% 0.62/0.80  # Proof found!
% 0.62/0.80  # SZS status Theorem
% 0.62/0.80  # SZS output start CNFRefutation
% 0.62/0.80  fof(t113_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.62/0.80  fof(l97_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 0.62/0.80  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.62/0.80  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.62/0.80  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.62/0.80  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.62/0.80  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.62/0.80  fof(c_0_7, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t113_zfmisc_1])).
% 0.62/0.80  fof(c_0_8, plain, ![X15, X16]:r1_xboole_0(k3_xboole_0(X15,X16),k5_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[l97_xboole_1])).
% 0.62/0.80  fof(c_0_9, plain, ![X18]:k5_xboole_0(X18,k1_xboole_0)=X18, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.62/0.80  fof(c_0_10, plain, ![X17]:k3_xboole_0(X17,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.62/0.80  fof(c_0_11, negated_conjecture, (((esk7_0!=k1_xboole_0|k2_zfmisc_1(esk7_0,esk8_0)!=k1_xboole_0)&(esk8_0!=k1_xboole_0|k2_zfmisc_1(esk7_0,esk8_0)!=k1_xboole_0))&(k2_zfmisc_1(esk7_0,esk8_0)=k1_xboole_0|(esk7_0=k1_xboole_0|esk8_0=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).
% 0.62/0.80  fof(c_0_12, plain, ![X19, X20, X21, X22, X25, X26, X27, X28, X29, X30, X32, X33]:(((((r2_hidden(esk2_4(X19,X20,X21,X22),X19)|~r2_hidden(X22,X21)|X21!=k2_zfmisc_1(X19,X20))&(r2_hidden(esk3_4(X19,X20,X21,X22),X20)|~r2_hidden(X22,X21)|X21!=k2_zfmisc_1(X19,X20)))&(X22=k4_tarski(esk2_4(X19,X20,X21,X22),esk3_4(X19,X20,X21,X22))|~r2_hidden(X22,X21)|X21!=k2_zfmisc_1(X19,X20)))&(~r2_hidden(X26,X19)|~r2_hidden(X27,X20)|X25!=k4_tarski(X26,X27)|r2_hidden(X25,X21)|X21!=k2_zfmisc_1(X19,X20)))&((~r2_hidden(esk4_3(X28,X29,X30),X30)|(~r2_hidden(X32,X28)|~r2_hidden(X33,X29)|esk4_3(X28,X29,X30)!=k4_tarski(X32,X33))|X30=k2_zfmisc_1(X28,X29))&(((r2_hidden(esk5_3(X28,X29,X30),X28)|r2_hidden(esk4_3(X28,X29,X30),X30)|X30=k2_zfmisc_1(X28,X29))&(r2_hidden(esk6_3(X28,X29,X30),X29)|r2_hidden(esk4_3(X28,X29,X30),X30)|X30=k2_zfmisc_1(X28,X29)))&(esk4_3(X28,X29,X30)=k4_tarski(esk5_3(X28,X29,X30),esk6_3(X28,X29,X30))|r2_hidden(esk4_3(X28,X29,X30),X30)|X30=k2_zfmisc_1(X28,X29))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.62/0.80  fof(c_0_13, plain, ![X9, X10, X12, X13, X14]:((r1_xboole_0(X9,X10)|r2_hidden(esk1_2(X9,X10),k3_xboole_0(X9,X10)))&(~r2_hidden(X14,k3_xboole_0(X12,X13))|~r1_xboole_0(X12,X13))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.62/0.80  cnf(c_0_14, plain, (r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.62/0.80  cnf(c_0_15, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.62/0.80  cnf(c_0_16, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.62/0.80  cnf(c_0_17, negated_conjecture, (k2_zfmisc_1(esk7_0,esk8_0)=k1_xboole_0|esk7_0=k1_xboole_0|esk8_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.62/0.80  cnf(c_0_18, plain, (r2_hidden(esk5_3(X1,X2,X3),X1)|r2_hidden(esk4_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.62/0.80  cnf(c_0_19, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.62/0.80  cnf(c_0_20, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 0.62/0.80  cnf(c_0_21, negated_conjecture, (esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|X1=k1_xboole_0|r2_hidden(esk5_3(esk7_0,esk8_0,X1),esk7_0)|r2_hidden(esk4_3(esk7_0,esk8_0,X1),X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.62/0.80  cnf(c_0_22, plain, (~r2_hidden(X1,k3_xboole_0(k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.62/0.80  cnf(c_0_23, negated_conjecture, (esk8_0!=k1_xboole_0|k2_zfmisc_1(esk7_0,esk8_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.62/0.80  cnf(c_0_24, negated_conjecture, (esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)|r2_hidden(esk5_3(esk7_0,esk8_0,esk8_0),esk7_0)), inference(ef,[status(thm)],[c_0_21])).
% 0.62/0.80  cnf(c_0_25, plain, (r2_hidden(esk6_3(X1,X2,X3),X2)|r2_hidden(esk4_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.62/0.80  cnf(c_0_26, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_22, c_0_16])).
% 0.62/0.80  cnf(c_0_27, negated_conjecture, (esk7_0!=k1_xboole_0|k2_zfmisc_1(esk7_0,esk8_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.62/0.80  cnf(c_0_28, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk5_3(esk7_0,esk8_0,esk8_0),esk7_0)|r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)|k2_zfmisc_1(esk7_0,k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.62/0.80  cnf(c_0_29, negated_conjecture, (r2_hidden(esk6_3(esk7_0,esk8_0,k1_xboole_0),esk8_0)|esk8_0!=k1_xboole_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_25])]), c_0_26])).
% 0.62/0.80  cnf(c_0_30, negated_conjecture, (esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|X1=k1_xboole_0|r2_hidden(esk6_3(esk7_0,esk8_0,X1),esk8_0)|r2_hidden(esk4_3(esk7_0,esk8_0,X1),X1)), inference(spm,[status(thm)],[c_0_17, c_0_25])).
% 0.62/0.80  cnf(c_0_31, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k4_tarski(X1,X3)|X6!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.62/0.80  cnf(c_0_32, negated_conjecture, (r2_hidden(esk5_3(esk7_0,esk8_0,k1_xboole_0),esk7_0)|esk7_0!=k1_xboole_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_18])]), c_0_26])).
% 0.62/0.80  cnf(c_0_33, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)|r2_hidden(esk5_3(esk7_0,esk8_0,esk8_0),esk7_0)), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_25]), c_0_26])]), c_0_26])).
% 0.62/0.80  cnf(c_0_34, negated_conjecture, (esk7_0=k1_xboole_0|X1=k1_xboole_0|r2_hidden(esk6_3(esk7_0,esk8_0,X1),esk8_0)|r2_hidden(esk4_3(esk7_0,esk8_0,X1),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_26])).
% 0.62/0.80  cnf(c_0_35, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_31])])).
% 0.62/0.80  cnf(c_0_36, negated_conjecture, (r2_hidden(esk5_3(esk7_0,esk8_0,esk8_0),esk7_0)|r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_26])).
% 0.62/0.80  cnf(c_0_37, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)|r2_hidden(esk6_3(esk7_0,esk8_0,esk8_0),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_34]), c_0_26])).
% 0.62/0.80  cnf(c_0_38, negated_conjecture, (r2_hidden(k4_tarski(esk5_3(esk7_0,esk8_0,esk8_0),X1),k2_zfmisc_1(esk7_0,X2))|r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.62/0.80  cnf(c_0_39, negated_conjecture, (r2_hidden(esk6_3(esk7_0,esk8_0,esk8_0),esk8_0)|r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_37]), c_0_26])).
% 0.62/0.80  cnf(c_0_40, negated_conjecture, (r2_hidden(k4_tarski(esk5_3(esk7_0,esk8_0,esk8_0),esk6_3(esk7_0,esk8_0,esk8_0)),k2_zfmisc_1(esk7_0,esk8_0))|r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.62/0.80  cnf(c_0_41, negated_conjecture, (esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_17]), c_0_26])).
% 0.62/0.80  cnf(c_0_42, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_41]), c_0_26])).
% 0.62/0.80  cnf(c_0_43, plain, (X1=X2|r2_hidden(esk5_3(X3,X4,X2),X3)|r2_hidden(esk4_3(X3,X4,X2),X2)|r2_hidden(esk5_3(X3,X4,X1),X3)|r2_hidden(esk4_3(X3,X4,X1),X1)), inference(spm,[status(thm)],[c_0_18, c_0_18])).
% 0.62/0.80  fof(c_0_44, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.62/0.80  cnf(c_0_45, negated_conjecture, (r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_42]), c_0_26])).
% 0.62/0.80  cnf(c_0_46, negated_conjecture, (r2_hidden(esk4_3(X1,X2,esk7_0),esk7_0)|r2_hidden(esk5_3(X1,X2,k1_xboole_0),X1)|r2_hidden(esk5_3(X1,X2,esk7_0),X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_43])]), c_0_26]), c_0_26])).
% 0.62/0.80  cnf(c_0_47, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.62/0.80  cnf(c_0_48, negated_conjecture, (r2_hidden(k4_tarski(esk4_3(esk7_0,esk8_0,esk8_0),X1),k2_zfmisc_1(esk8_0,X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_35, c_0_45])).
% 0.62/0.80  cnf(c_0_49, negated_conjecture, (r2_hidden(esk4_3(k1_xboole_0,X1,esk7_0),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_46]), c_0_26])).
% 0.62/0.80  cnf(c_0_50, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_47])).
% 0.62/0.80  cnf(c_0_51, negated_conjecture, (r2_hidden(k4_tarski(esk4_3(esk7_0,esk8_0,esk8_0),esk4_3(k1_xboole_0,X1,esk7_0)),k2_zfmisc_1(esk8_0,esk7_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.62/0.80  cnf(c_0_52, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|r2_hidden(esk6_3(X1,X2,k1_xboole_0),X2)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_25]), c_0_50]), c_0_50]), c_0_50]), c_0_26])).
% 0.62/0.80  cnf(c_0_53, negated_conjecture, (r2_hidden(k4_tarski(X1,esk4_3(esk7_0,esk8_0,esk8_0)),k2_zfmisc_1(X2,esk8_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_35, c_0_45])).
% 0.62/0.80  cnf(c_0_54, negated_conjecture, (r2_hidden(esk6_3(esk8_0,esk7_0,k1_xboole_0),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_26])).
% 0.62/0.80  cnf(c_0_55, negated_conjecture, (r2_hidden(k4_tarski(esk6_3(esk8_0,esk7_0,k1_xboole_0),esk4_3(esk7_0,esk8_0,esk8_0)),k2_zfmisc_1(esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.62/0.80  cnf(c_0_56, negated_conjecture, (esk8_0=k1_xboole_0|esk7_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_17]), c_0_26])).
% 0.62/0.80  cnf(c_0_57, negated_conjecture, (esk7_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_56]), c_0_26])).
% 0.62/0.80  cnf(c_0_58, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_57]), c_0_57]), c_0_26]), ['proof']).
% 0.62/0.80  # SZS output end CNFRefutation
% 0.62/0.80  # Proof object total steps             : 59
% 0.62/0.80  # Proof object clause steps            : 44
% 0.62/0.80  # Proof object formula steps           : 15
% 0.62/0.80  # Proof object conjectures             : 32
% 0.62/0.80  # Proof object clause conjectures      : 29
% 0.62/0.80  # Proof object formula conjectures     : 3
% 0.62/0.80  # Proof object initial clauses used    : 11
% 0.62/0.80  # Proof object initial formulas used   : 7
% 0.62/0.80  # Proof object generating inferences   : 31
% 0.62/0.80  # Proof object simplifying inferences  : 31
% 0.62/0.80  # Training examples: 0 positive, 0 negative
% 0.62/0.80  # Parsed axioms                        : 7
% 0.62/0.80  # Removed by relevancy pruning/SinE    : 0
% 0.62/0.80  # Initial clauses                      : 17
% 0.62/0.80  # Removed in clause preprocessing      : 0
% 0.62/0.80  # Initial clauses in saturation        : 17
% 0.62/0.80  # Processed clauses                    : 1228
% 0.62/0.80  # ...of these trivial                  : 93
% 0.62/0.80  # ...subsumed                          : 702
% 0.62/0.80  # ...remaining for further processing  : 433
% 0.62/0.80  # Other redundant clauses eliminated   : 392
% 0.62/0.80  # Clauses deleted for lack of memory   : 0
% 0.62/0.80  # Backward-subsumed                    : 41
% 0.62/0.80  # Backward-rewritten                   : 138
% 0.62/0.80  # Generated clauses                    : 42111
% 0.62/0.80  # ...of the previous two non-trivial   : 38540
% 0.62/0.80  # Contextual simplify-reflections      : 12
% 0.62/0.80  # Paramodulations                      : 41689
% 0.62/0.80  # Factorizations                       : 30
% 0.62/0.80  # Equation resolutions                 : 393
% 0.62/0.80  # Propositional unsat checks           : 0
% 0.62/0.80  #    Propositional check models        : 0
% 0.62/0.80  #    Propositional check unsatisfiable : 0
% 0.62/0.80  #    Propositional clauses             : 0
% 0.62/0.80  #    Propositional clauses after purity: 0
% 0.62/0.80  #    Propositional unsat core size     : 0
% 0.62/0.80  #    Propositional preprocessing time  : 0.000
% 0.62/0.80  #    Propositional encoding time       : 0.000
% 0.62/0.80  #    Propositional solver time         : 0.000
% 0.62/0.80  #    Success case prop preproc time    : 0.000
% 0.62/0.80  #    Success case prop encoding time   : 0.000
% 0.62/0.80  #    Success case prop solver time     : 0.000
% 0.62/0.80  # Current number of processed clauses  : 233
% 0.62/0.80  #    Positive orientable unit clauses  : 64
% 0.62/0.80  #    Positive unorientable unit clauses: 1
% 0.62/0.80  #    Negative unit clauses             : 3
% 0.62/0.80  #    Non-unit-clauses                  : 165
% 0.62/0.80  # Current number of unprocessed clauses: 36919
% 0.62/0.80  # ...number of literals in the above   : 155736
% 0.62/0.80  # Current number of archived formulas  : 0
% 0.62/0.80  # Current number of archived clauses   : 196
% 0.62/0.80  # Clause-clause subsumption calls (NU) : 11057
% 0.62/0.80  # Rec. Clause-clause subsumption calls : 3359
% 0.62/0.80  # Non-unit clause-clause subsumptions  : 639
% 0.62/0.80  # Unit Clause-clause subsumption calls : 203
% 0.62/0.80  # Rewrite failures with RHS unbound    : 0
% 0.62/0.80  # BW rewrite match attempts            : 116
% 0.62/0.80  # BW rewrite match successes           : 16
% 0.62/0.80  # Condensation attempts                : 0
% 0.62/0.80  # Condensation successes               : 0
% 0.62/0.80  # Termbank termtop insertions          : 906047
% 0.62/0.81  
% 0.62/0.81  # -------------------------------------------------
% 0.62/0.81  # User time                : 0.441 s
% 0.62/0.81  # System time              : 0.022 s
% 0.62/0.81  # Total time               : 0.463 s
% 0.62/0.81  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
