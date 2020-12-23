%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:28 EST 2020

% Result     : Theorem 0.42s
% Output     : CNFRefutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   61 (2567 expanded)
%              Number of clauses        :   42 (1119 expanded)
%              Number of leaves         :    9 ( 698 expanded)
%              Depth                    :   19
%              Number of atoms          :  168 (6197 expanded)
%              Number of equality atoms :   68 (2707 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l97_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t113_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

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

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(c_0_9,plain,(
    ! [X13,X14] : r1_xboole_0(k3_xboole_0(X13,X14),k5_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[l97_xboole_1])).

fof(c_0_10,plain,(
    ! [X19] : k5_xboole_0(X19,k1_xboole_0) = X19 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_11,plain,(
    ! [X17] : k3_xboole_0(X17,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_12,plain,(
    ! [X18] :
      ( ~ r1_tarski(X18,k1_xboole_0)
      | X18 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

fof(c_0_13,plain,(
    ! [X15,X16] : r1_tarski(k3_xboole_0(X15,X16),X15) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k1_xboole_0
      <=> ( X1 = k1_xboole_0
          | X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t113_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X7,X8,X10,X11,X12] :
      ( ( r1_xboole_0(X7,X8)
        | r2_hidden(esk1_2(X7,X8),k3_xboole_0(X7,X8)) )
      & ( ~ r2_hidden(X12,k3_xboole_0(X10,X11))
        | ~ r1_xboole_0(X10,X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_16,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,negated_conjecture,
    ( ( esk7_0 != k1_xboole_0
      | k2_zfmisc_1(esk7_0,esk8_0) != k1_xboole_0 )
    & ( esk8_0 != k1_xboole_0
      | k2_zfmisc_1(esk7_0,esk8_0) != k1_xboole_0 )
    & ( k2_zfmisc_1(esk7_0,esk8_0) = k1_xboole_0
      | esk7_0 = k1_xboole_0
      | esk8_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])).

fof(c_0_22,plain,(
    ! [X20,X21,X22,X23,X26,X27,X28,X29,X30,X31,X33,X34] :
      ( ( r2_hidden(esk2_4(X20,X21,X22,X23),X20)
        | ~ r2_hidden(X23,X22)
        | X22 != k2_zfmisc_1(X20,X21) )
      & ( r2_hidden(esk3_4(X20,X21,X22,X23),X21)
        | ~ r2_hidden(X23,X22)
        | X22 != k2_zfmisc_1(X20,X21) )
      & ( X23 = k4_tarski(esk2_4(X20,X21,X22,X23),esk3_4(X20,X21,X22,X23))
        | ~ r2_hidden(X23,X22)
        | X22 != k2_zfmisc_1(X20,X21) )
      & ( ~ r2_hidden(X27,X20)
        | ~ r2_hidden(X28,X21)
        | X26 != k4_tarski(X27,X28)
        | r2_hidden(X26,X22)
        | X22 != k2_zfmisc_1(X20,X21) )
      & ( ~ r2_hidden(esk4_3(X29,X30,X31),X31)
        | ~ r2_hidden(X33,X29)
        | ~ r2_hidden(X34,X30)
        | esk4_3(X29,X30,X31) != k4_tarski(X33,X34)
        | X31 = k2_zfmisc_1(X29,X30) )
      & ( r2_hidden(esk5_3(X29,X30,X31),X29)
        | r2_hidden(esk4_3(X29,X30,X31),X31)
        | X31 = k2_zfmisc_1(X29,X30) )
      & ( r2_hidden(esk6_3(X29,X30,X31),X30)
        | r2_hidden(esk4_3(X29,X30,X31),X31)
        | X31 = k2_zfmisc_1(X29,X30) )
      & ( esk4_3(X29,X30,X31) = k4_tarski(esk5_3(X29,X30,X31),esk6_3(X29,X30,X31))
        | r2_hidden(esk4_3(X29,X30,X31),X31)
        | X31 = k2_zfmisc_1(X29,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_25,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( k2_zfmisc_1(esk7_0,esk8_0) = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X1)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( esk8_0 != k1_xboole_0
    | k2_zfmisc_1(esk7_0,esk8_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | r2_hidden(esk5_3(esk7_0,esk8_0,X1),esk7_0)
    | r2_hidden(esk4_3(esk7_0,esk8_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | k2_zfmisc_1(esk7_0,esk8_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk6_3(esk7_0,esk8_0,k1_xboole_0),esk8_0)
    | esk8_0 != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29])]),c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)
    | r2_hidden(esk5_3(esk7_0,esk8_0,esk8_0),esk7_0) ),
    inference(ef,[status(thm)],[c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | r2_hidden(esk6_3(esk7_0,esk8_0,X1),esk8_0)
    | r2_hidden(esk4_3(esk7_0,esk8_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_29])).

fof(c_0_36,plain,(
    ! [X37,X38,X39,X40] :
      ( ( r2_hidden(X37,X39)
        | ~ r2_hidden(k4_tarski(X37,X38),k2_zfmisc_1(X39,X40)) )
      & ( r2_hidden(X38,X40)
        | ~ r2_hidden(k4_tarski(X37,X38),k2_zfmisc_1(X39,X40)) )
      & ( ~ r2_hidden(X37,X39)
        | ~ r2_hidden(X38,X40)
        | r2_hidden(k4_tarski(X37,X38),k2_zfmisc_1(X39,X40)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk5_3(esk7_0,esk8_0,k1_xboole_0),esk7_0)
    | esk7_0 != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_27])]),c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk5_3(esk7_0,esk8_0,esk8_0),esk7_0)
    | r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)
    | r2_hidden(esk6_3(esk7_0,esk8_0,esk8_0),esk8_0) ),
    inference(ef,[status(thm)],[c_0_35])).

cnf(c_0_40,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)
    | r2_hidden(esk5_3(esk7_0,esk8_0,esk8_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk6_3(esk7_0,esk8_0,esk8_0),esk8_0)
    | r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_39]),c_0_30])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_3(esk7_0,esk8_0,esk8_0),X1),k2_zfmisc_1(esk7_0,X2))
    | r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)
    | r2_hidden(esk6_3(esk7_0,esk8_0,esk8_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_42]),c_0_30])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_3(esk7_0,esk8_0,esk8_0),esk6_3(esk7_0,esk8_0,esk8_0)),k2_zfmisc_1(esk7_0,esk8_0))
    | r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_46,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_26]),c_0_30])).

cnf(c_0_47,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_46]),c_0_30])).

cnf(c_0_48,plain,
    ( X1 = X2
    | r2_hidden(esk5_3(X3,X4,X2),X3)
    | r2_hidden(esk4_3(X3,X4,X2),X2)
    | r2_hidden(esk5_3(X3,X4,X1),X3)
    | r2_hidden(esk4_3(X3,X4,X1),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_27])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_47]),c_0_30])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk4_3(X1,X2,esk7_0),esk7_0)
    | r2_hidden(esk5_3(X1,X2,k1_xboole_0),X1)
    | r2_hidden(esk5_3(X1,X2,esk7_0),X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_48])]),c_0_30]),c_0_30])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_3(esk7_0,esk8_0,esk8_0),X1),k2_zfmisc_1(esk8_0,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk4_3(k1_xboole_0,X1,esk7_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_50]),c_0_30])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_3(esk7_0,esk8_0,esk8_0),esk4_3(k1_xboole_0,X1,esk7_0)),k2_zfmisc_1(esk8_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_54,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | r2_hidden(esk6_3(X1,X2,k1_xboole_0),X2) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_29]),c_0_25]),c_0_25]),c_0_25]),c_0_30])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk4_3(esk7_0,esk8_0,esk8_0)),k2_zfmisc_1(X2,esk8_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk6_3(esk8_0,esk7_0,k1_xboole_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_30])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_3(esk8_0,esk7_0,k1_xboole_0),esk4_3(esk7_0,esk8_0,esk8_0)),k2_zfmisc_1(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_58,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_26]),c_0_30])).

cnf(c_0_59,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_58]),c_0_30])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_59]),c_0_59]),c_0_30]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.42/0.59  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.42/0.59  # and selection function SelectNegativeLiterals.
% 0.42/0.59  #
% 0.42/0.59  # Preprocessing time       : 0.027 s
% 0.42/0.59  # Presaturation interreduction done
% 0.42/0.59  
% 0.42/0.59  # Proof found!
% 0.42/0.59  # SZS status Theorem
% 0.42/0.59  # SZS output start CNFRefutation
% 0.42/0.59  fof(l97_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 0.42/0.59  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.42/0.59  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.42/0.59  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.42/0.59  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.42/0.59  fof(t113_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.42/0.59  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.42/0.59  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.42/0.59  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.42/0.59  fof(c_0_9, plain, ![X13, X14]:r1_xboole_0(k3_xboole_0(X13,X14),k5_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[l97_xboole_1])).
% 0.42/0.59  fof(c_0_10, plain, ![X19]:k5_xboole_0(X19,k1_xboole_0)=X19, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.42/0.59  fof(c_0_11, plain, ![X17]:k3_xboole_0(X17,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.42/0.59  fof(c_0_12, plain, ![X18]:(~r1_tarski(X18,k1_xboole_0)|X18=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.42/0.59  fof(c_0_13, plain, ![X15, X16]:r1_tarski(k3_xboole_0(X15,X16),X15), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.42/0.59  fof(c_0_14, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t113_zfmisc_1])).
% 0.42/0.59  fof(c_0_15, plain, ![X7, X8, X10, X11, X12]:((r1_xboole_0(X7,X8)|r2_hidden(esk1_2(X7,X8),k3_xboole_0(X7,X8)))&(~r2_hidden(X12,k3_xboole_0(X10,X11))|~r1_xboole_0(X10,X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.42/0.59  cnf(c_0_16, plain, (r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.42/0.59  cnf(c_0_17, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.42/0.59  cnf(c_0_18, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.42/0.59  cnf(c_0_19, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.42/0.59  cnf(c_0_20, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.42/0.59  fof(c_0_21, negated_conjecture, (((esk7_0!=k1_xboole_0|k2_zfmisc_1(esk7_0,esk8_0)!=k1_xboole_0)&(esk8_0!=k1_xboole_0|k2_zfmisc_1(esk7_0,esk8_0)!=k1_xboole_0))&(k2_zfmisc_1(esk7_0,esk8_0)=k1_xboole_0|(esk7_0=k1_xboole_0|esk8_0=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])).
% 0.42/0.59  fof(c_0_22, plain, ![X20, X21, X22, X23, X26, X27, X28, X29, X30, X31, X33, X34]:(((((r2_hidden(esk2_4(X20,X21,X22,X23),X20)|~r2_hidden(X23,X22)|X22!=k2_zfmisc_1(X20,X21))&(r2_hidden(esk3_4(X20,X21,X22,X23),X21)|~r2_hidden(X23,X22)|X22!=k2_zfmisc_1(X20,X21)))&(X23=k4_tarski(esk2_4(X20,X21,X22,X23),esk3_4(X20,X21,X22,X23))|~r2_hidden(X23,X22)|X22!=k2_zfmisc_1(X20,X21)))&(~r2_hidden(X27,X20)|~r2_hidden(X28,X21)|X26!=k4_tarski(X27,X28)|r2_hidden(X26,X22)|X22!=k2_zfmisc_1(X20,X21)))&((~r2_hidden(esk4_3(X29,X30,X31),X31)|(~r2_hidden(X33,X29)|~r2_hidden(X34,X30)|esk4_3(X29,X30,X31)!=k4_tarski(X33,X34))|X31=k2_zfmisc_1(X29,X30))&(((r2_hidden(esk5_3(X29,X30,X31),X29)|r2_hidden(esk4_3(X29,X30,X31),X31)|X31=k2_zfmisc_1(X29,X30))&(r2_hidden(esk6_3(X29,X30,X31),X30)|r2_hidden(esk4_3(X29,X30,X31),X31)|X31=k2_zfmisc_1(X29,X30)))&(esk4_3(X29,X30,X31)=k4_tarski(esk5_3(X29,X30,X31),esk6_3(X29,X30,X31))|r2_hidden(esk4_3(X29,X30,X31),X31)|X31=k2_zfmisc_1(X29,X30))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.42/0.59  cnf(c_0_23, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.42/0.59  cnf(c_0_24, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.42/0.59  cnf(c_0_25, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.42/0.59  cnf(c_0_26, negated_conjecture, (k2_zfmisc_1(esk7_0,esk8_0)=k1_xboole_0|esk7_0=k1_xboole_0|esk8_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.42/0.59  cnf(c_0_27, plain, (r2_hidden(esk5_3(X1,X2,X3),X1)|r2_hidden(esk4_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.42/0.59  cnf(c_0_28, negated_conjecture, (esk8_0!=k1_xboole_0|k2_zfmisc_1(esk7_0,esk8_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.42/0.59  cnf(c_0_29, plain, (r2_hidden(esk6_3(X1,X2,X3),X2)|r2_hidden(esk4_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.42/0.59  cnf(c_0_30, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.42/0.59  cnf(c_0_31, negated_conjecture, (esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|X1=k1_xboole_0|r2_hidden(esk5_3(esk7_0,esk8_0,X1),esk7_0)|r2_hidden(esk4_3(esk7_0,esk8_0,X1),X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.42/0.59  cnf(c_0_32, negated_conjecture, (esk7_0!=k1_xboole_0|k2_zfmisc_1(esk7_0,esk8_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.42/0.59  cnf(c_0_33, negated_conjecture, (r2_hidden(esk6_3(esk7_0,esk8_0,k1_xboole_0),esk8_0)|esk8_0!=k1_xboole_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29])]), c_0_30])).
% 0.42/0.59  cnf(c_0_34, negated_conjecture, (esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)|r2_hidden(esk5_3(esk7_0,esk8_0,esk8_0),esk7_0)), inference(ef,[status(thm)],[c_0_31])).
% 0.42/0.59  cnf(c_0_35, negated_conjecture, (esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|X1=k1_xboole_0|r2_hidden(esk6_3(esk7_0,esk8_0,X1),esk8_0)|r2_hidden(esk4_3(esk7_0,esk8_0,X1),X1)), inference(spm,[status(thm)],[c_0_26, c_0_29])).
% 0.42/0.59  fof(c_0_36, plain, ![X37, X38, X39, X40]:(((r2_hidden(X37,X39)|~r2_hidden(k4_tarski(X37,X38),k2_zfmisc_1(X39,X40)))&(r2_hidden(X38,X40)|~r2_hidden(k4_tarski(X37,X38),k2_zfmisc_1(X39,X40))))&(~r2_hidden(X37,X39)|~r2_hidden(X38,X40)|r2_hidden(k4_tarski(X37,X38),k2_zfmisc_1(X39,X40)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.42/0.59  cnf(c_0_37, negated_conjecture, (r2_hidden(esk5_3(esk7_0,esk8_0,k1_xboole_0),esk7_0)|esk7_0!=k1_xboole_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_27])]), c_0_30])).
% 0.42/0.59  cnf(c_0_38, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk5_3(esk7_0,esk8_0,esk8_0),esk7_0)|r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_30])).
% 0.42/0.59  cnf(c_0_39, negated_conjecture, (esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)|r2_hidden(esk6_3(esk7_0,esk8_0,esk8_0),esk8_0)), inference(ef,[status(thm)],[c_0_35])).
% 0.42/0.59  cnf(c_0_40, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.42/0.59  cnf(c_0_41, negated_conjecture, (r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)|r2_hidden(esk5_3(esk7_0,esk8_0,esk8_0),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_30])).
% 0.42/0.59  cnf(c_0_42, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk6_3(esk7_0,esk8_0,esk8_0),esk8_0)|r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_39]), c_0_30])).
% 0.42/0.59  cnf(c_0_43, negated_conjecture, (r2_hidden(k4_tarski(esk5_3(esk7_0,esk8_0,esk8_0),X1),k2_zfmisc_1(esk7_0,X2))|r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.42/0.59  cnf(c_0_44, negated_conjecture, (r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)|r2_hidden(esk6_3(esk7_0,esk8_0,esk8_0),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_42]), c_0_30])).
% 0.42/0.59  cnf(c_0_45, negated_conjecture, (r2_hidden(k4_tarski(esk5_3(esk7_0,esk8_0,esk8_0),esk6_3(esk7_0,esk8_0,esk8_0)),k2_zfmisc_1(esk7_0,esk8_0))|r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.42/0.59  cnf(c_0_46, negated_conjecture, (esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_26]), c_0_30])).
% 0.42/0.59  cnf(c_0_47, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_46]), c_0_30])).
% 0.42/0.59  cnf(c_0_48, plain, (X1=X2|r2_hidden(esk5_3(X3,X4,X2),X3)|r2_hidden(esk4_3(X3,X4,X2),X2)|r2_hidden(esk5_3(X3,X4,X1),X3)|r2_hidden(esk4_3(X3,X4,X1),X1)), inference(spm,[status(thm)],[c_0_27, c_0_27])).
% 0.42/0.59  cnf(c_0_49, negated_conjecture, (r2_hidden(esk4_3(esk7_0,esk8_0,esk8_0),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_47]), c_0_30])).
% 0.42/0.59  cnf(c_0_50, negated_conjecture, (r2_hidden(esk4_3(X1,X2,esk7_0),esk7_0)|r2_hidden(esk5_3(X1,X2,k1_xboole_0),X1)|r2_hidden(esk5_3(X1,X2,esk7_0),X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_48])]), c_0_30]), c_0_30])).
% 0.42/0.59  cnf(c_0_51, negated_conjecture, (r2_hidden(k4_tarski(esk4_3(esk7_0,esk8_0,esk8_0),X1),k2_zfmisc_1(esk8_0,X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_40, c_0_49])).
% 0.42/0.59  cnf(c_0_52, negated_conjecture, (r2_hidden(esk4_3(k1_xboole_0,X1,esk7_0),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_50]), c_0_30])).
% 0.42/0.59  cnf(c_0_53, negated_conjecture, (r2_hidden(k4_tarski(esk4_3(esk7_0,esk8_0,esk8_0),esk4_3(k1_xboole_0,X1,esk7_0)),k2_zfmisc_1(esk8_0,esk7_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.42/0.59  cnf(c_0_54, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|r2_hidden(esk6_3(X1,X2,k1_xboole_0),X2)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_29]), c_0_25]), c_0_25]), c_0_25]), c_0_30])).
% 0.42/0.59  cnf(c_0_55, negated_conjecture, (r2_hidden(k4_tarski(X1,esk4_3(esk7_0,esk8_0,esk8_0)),k2_zfmisc_1(X2,esk8_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_40, c_0_49])).
% 0.42/0.59  cnf(c_0_56, negated_conjecture, (r2_hidden(esk6_3(esk8_0,esk7_0,k1_xboole_0),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_30])).
% 0.42/0.59  cnf(c_0_57, negated_conjecture, (r2_hidden(k4_tarski(esk6_3(esk8_0,esk7_0,k1_xboole_0),esk4_3(esk7_0,esk8_0,esk8_0)),k2_zfmisc_1(esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.42/0.59  cnf(c_0_58, negated_conjecture, (esk8_0=k1_xboole_0|esk7_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_26]), c_0_30])).
% 0.42/0.59  cnf(c_0_59, negated_conjecture, (esk7_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_58]), c_0_30])).
% 0.42/0.59  cnf(c_0_60, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_59]), c_0_59]), c_0_30]), ['proof']).
% 0.42/0.59  # SZS output end CNFRefutation
% 0.42/0.59  # Proof object total steps             : 61
% 0.42/0.59  # Proof object clause steps            : 42
% 0.42/0.59  # Proof object formula steps           : 19
% 0.42/0.59  # Proof object conjectures             : 31
% 0.42/0.59  # Proof object clause conjectures      : 28
% 0.42/0.59  # Proof object formula conjectures     : 3
% 0.42/0.59  # Proof object initial clauses used    : 12
% 0.42/0.59  # Proof object initial formulas used   : 9
% 0.42/0.59  # Proof object generating inferences   : 29
% 0.42/0.59  # Proof object simplifying inferences  : 27
% 0.42/0.59  # Training examples: 0 positive, 0 negative
% 0.42/0.59  # Parsed axioms                        : 9
% 0.42/0.59  # Removed by relevancy pruning/SinE    : 0
% 0.42/0.59  # Initial clauses                      : 21
% 0.42/0.59  # Removed in clause preprocessing      : 0
% 0.42/0.59  # Initial clauses in saturation        : 21
% 0.42/0.59  # Processed clauses                    : 779
% 0.42/0.59  # ...of these trivial                  : 25
% 0.42/0.59  # ...subsumed                          : 421
% 0.42/0.59  # ...remaining for further processing  : 333
% 0.42/0.59  # Other redundant clauses eliminated   : 311
% 0.42/0.59  # Clauses deleted for lack of memory   : 0
% 0.42/0.59  # Backward-subsumed                    : 32
% 0.42/0.59  # Backward-rewritten                   : 113
% 0.42/0.59  # Generated clauses                    : 20079
% 0.42/0.59  # ...of the previous two non-trivial   : 18127
% 0.42/0.59  # Contextual simplify-reflections      : 2
% 0.42/0.59  # Paramodulations                      : 19755
% 0.42/0.59  # Factorizations                       : 14
% 0.42/0.59  # Equation resolutions                 : 311
% 0.42/0.59  # Propositional unsat checks           : 0
% 0.42/0.59  #    Propositional check models        : 0
% 0.42/0.59  #    Propositional check unsatisfiable : 0
% 0.42/0.59  #    Propositional clauses             : 0
% 0.42/0.59  #    Propositional clauses after purity: 0
% 0.42/0.59  #    Propositional unsat core size     : 0
% 0.42/0.59  #    Propositional preprocessing time  : 0.000
% 0.42/0.59  #    Propositional encoding time       : 0.000
% 0.42/0.59  #    Propositional solver time         : 0.000
% 0.42/0.59  #    Success case prop preproc time    : 0.000
% 0.42/0.59  #    Success case prop encoding time   : 0.000
% 0.42/0.59  #    Success case prop solver time     : 0.000
% 0.42/0.59  # Current number of processed clauses  : 164
% 0.42/0.59  #    Positive orientable unit clauses  : 39
% 0.42/0.59  #    Positive unorientable unit clauses: 0
% 0.42/0.59  #    Negative unit clauses             : 2
% 0.42/0.59  #    Non-unit-clauses                  : 123
% 0.42/0.59  # Current number of unprocessed clauses: 17083
% 0.42/0.59  # ...number of literals in the above   : 66371
% 0.42/0.59  # Current number of archived formulas  : 0
% 0.42/0.59  # Current number of archived clauses   : 165
% 0.42/0.59  # Clause-clause subsumption calls (NU) : 5742
% 0.42/0.59  # Rec. Clause-clause subsumption calls : 2075
% 0.42/0.59  # Non-unit clause-clause subsumptions  : 388
% 0.42/0.59  # Unit Clause-clause subsumption calls : 207
% 0.42/0.59  # Rewrite failures with RHS unbound    : 0
% 0.42/0.59  # BW rewrite match attempts            : 46
% 0.42/0.59  # BW rewrite match successes           : 4
% 0.42/0.59  # Condensation attempts                : 0
% 0.42/0.59  # Condensation successes               : 0
% 0.42/0.59  # Termbank termtop insertions          : 399463
% 0.42/0.59  
% 0.42/0.59  # -------------------------------------------------
% 0.42/0.59  # User time                : 0.230 s
% 0.42/0.59  # System time              : 0.019 s
% 0.42/0.59  # Total time               : 0.249 s
% 0.42/0.59  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
