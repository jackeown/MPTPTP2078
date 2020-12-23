%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t56_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:10 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   91 (25714 expanded)
%              Number of clauses        :   77 (12563 expanded)
%              Number of leaves         :    7 (7300 expanded)
%              Depth                    :   25
%              Number of atoms          :  265 (70705 expanded)
%              Number of equality atoms :  259 (58224 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t56_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k4_zfmisc_1(X1,X2,X3,X4) = k4_zfmisc_1(X5,X6,X7,X8)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | X3 = k1_xboole_0
        | X4 = k1_xboole_0
        | ( X1 = X5
          & X2 = X6
          & X3 = X7
          & X4 = X8 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t56_mcart_1.p',t56_mcart_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t56_mcart_1.p',t6_boole)).

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t56_mcart_1.p',d4_zfmisc_1)).

fof(t35_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 )
    <=> k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t56_mcart_1.p',t35_mcart_1)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t56_mcart_1.p',dt_o_0_0_xboole_0)).

fof(t134_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t56_mcart_1.p',t134_zfmisc_1)).

fof(t36_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k3_zfmisc_1(X1,X2,X3) = k3_zfmisc_1(X4,X5,X6)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | X3 = k1_xboole_0
        | ( X1 = X4
          & X2 = X5
          & X3 = X6 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t56_mcart_1.p',t36_mcart_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] :
        ( k4_zfmisc_1(X1,X2,X3,X4) = k4_zfmisc_1(X5,X6,X7,X8)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k1_xboole_0
          | ( X1 = X5
            & X2 = X6
            & X3 = X7
            & X4 = X8 ) ) ) ),
    inference(assume_negation,[status(cth)],[t56_mcart_1])).

fof(c_0_8,plain,(
    ! [X42] :
      ( ~ v1_xboole_0(X42)
      | X42 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_9,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) = k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)
    & esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & ( esk1_0 != esk5_0
      | esk2_0 != esk6_0
      | esk3_0 != esk7_0
      | esk4_0 != esk8_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X19,X20,X21,X22] : k4_zfmisc_1(X19,X20,X21,X22) = k2_zfmisc_1(k3_zfmisc_1(X19,X20,X21),X22) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X33,X34,X35] :
      ( ( X33 = k1_xboole_0
        | X34 = k1_xboole_0
        | X35 = k1_xboole_0
        | k3_zfmisc_1(X33,X34,X35) != k1_xboole_0 )
      & ( X33 != k1_xboole_0
        | k3_zfmisc_1(X33,X34,X35) = k1_xboole_0 )
      & ( X34 != k1_xboole_0
        | k3_zfmisc_1(X33,X34,X35) = k1_xboole_0 )
      & ( X35 != k1_xboole_0
        | k3_zfmisc_1(X33,X34,X35) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).

cnf(c_0_12,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

fof(c_0_14,plain,(
    ! [X25,X26,X27,X28] :
      ( ( X25 = X27
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | k2_zfmisc_1(X25,X26) != k2_zfmisc_1(X27,X28) )
      & ( X26 = X28
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | k2_zfmisc_1(X25,X26) != k2_zfmisc_1(X27,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_zfmisc_1])])])).

cnf(c_0_15,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) = k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k3_zfmisc_1(X2,X1,X3) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( k3_zfmisc_1(X2,X3,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(X3,X1) != k2_zfmisc_1(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( k2_zfmisc_1(k3_zfmisc_1(esk5_0,esk6_0,esk7_0),esk8_0) = k2_zfmisc_1(k3_zfmisc_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_16])).

cnf(c_0_22,plain,
    ( k3_zfmisc_1(X1,X2,X3) = o_0_0_xboole_0
    | X2 != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,plain,
    ( k3_zfmisc_1(X1,X2,X3) = o_0_0_xboole_0
    | X3 != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_18]),c_0_18])).

cnf(c_0_25,plain,
    ( X1 = o_0_0_xboole_0
    | X2 = o_0_0_xboole_0
    | X1 = X3
    | k2_zfmisc_1(X2,X1) != k2_zfmisc_1(X4,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_18]),c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( k2_zfmisc_1(k3_zfmisc_1(esk1_0,esk2_0,esk3_0),esk4_0) = k2_zfmisc_1(o_0_0_xboole_0,esk8_0)
    | esk6_0 != o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( esk4_0 != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[c_0_23,c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( k2_zfmisc_1(k3_zfmisc_1(esk1_0,esk2_0,esk3_0),esk4_0) = k2_zfmisc_1(o_0_0_xboole_0,esk8_0)
    | esk7_0 != o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_24])).

cnf(c_0_29,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = o_0_0_xboole_0
    | esk4_0 = X1
    | k2_zfmisc_1(o_0_0_xboole_0,esk8_0) != k2_zfmisc_1(X2,X1)
    | esk6_0 != o_0_0_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_33,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = o_0_0_xboole_0
    | esk4_0 = X1
    | k2_zfmisc_1(o_0_0_xboole_0,esk8_0) != k2_zfmisc_1(X2,X1)
    | esk7_0 != o_0_0_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_28]),c_0_27])).

cnf(c_0_35,plain,
    ( X1 = o_0_0_xboole_0
    | X2 = o_0_0_xboole_0
    | X3 = o_0_0_xboole_0
    | k3_zfmisc_1(X1,X2,X3) != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_18]),c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_36,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = o_0_0_xboole_0
    | esk8_0 = esk4_0
    | esk6_0 != o_0_0_xboole_0 ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( esk1_0 != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[c_0_31,c_0_18])).

cnf(c_0_38,negated_conjecture,
    ( esk2_0 != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[c_0_32,c_0_18])).

cnf(c_0_39,negated_conjecture,
    ( esk3_0 != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[c_0_33,c_0_18])).

cnf(c_0_40,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = o_0_0_xboole_0
    | esk8_0 = esk4_0
    | esk7_0 != o_0_0_xboole_0 ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( esk8_0 = esk4_0
    | esk6_0 != o_0_0_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( esk8_0 = esk4_0
    | esk7_0 != o_0_0_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_40]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( X1 = esk8_0
    | X2 = o_0_0_xboole_0
    | X1 = o_0_0_xboole_0
    | k2_zfmisc_1(X2,X1) != k2_zfmisc_1(k3_zfmisc_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_21])).

cnf(c_0_44,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_45,negated_conjecture,
    ( k2_zfmisc_1(k3_zfmisc_1(esk5_0,esk6_0,esk7_0),esk4_0) = k2_zfmisc_1(k3_zfmisc_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | esk6_0 != o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( k2_zfmisc_1(k3_zfmisc_1(esk5_0,esk6_0,esk7_0),esk4_0) = k2_zfmisc_1(k3_zfmisc_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | esk7_0 != o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = o_0_0_xboole_0
    | esk8_0 = esk4_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_43]),c_0_27])).

cnf(c_0_48,plain,
    ( X1 = X2
    | X1 = k1_xboole_0
    | X3 = k1_xboole_0
    | k2_zfmisc_1(X1,X3) != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_49,plain,
    ( k3_zfmisc_1(X1,X2,X3) = o_0_0_xboole_0
    | X1 != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_18]),c_0_18])).

cnf(c_0_50,negated_conjecture,
    ( k2_zfmisc_1(k3_zfmisc_1(esk1_0,esk2_0,esk3_0),esk4_0) = k2_zfmisc_1(o_0_0_xboole_0,esk4_0)
    | esk6_0 != o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_22])).

cnf(c_0_51,negated_conjecture,
    ( k2_zfmisc_1(k3_zfmisc_1(esk1_0,esk2_0,esk3_0),esk4_0) = k2_zfmisc_1(o_0_0_xboole_0,esk4_0)
    | esk7_0 != o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_24])).

cnf(c_0_52,negated_conjecture,
    ( esk8_0 = esk4_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_47]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_53,plain,
    ( X1 = o_0_0_xboole_0
    | X2 = o_0_0_xboole_0
    | X1 = X3
    | k2_zfmisc_1(X1,X2) != k2_zfmisc_1(X3,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_18]),c_0_18])).

cnf(c_0_54,negated_conjecture,
    ( k2_zfmisc_1(k3_zfmisc_1(esk1_0,esk2_0,esk3_0),esk4_0) = k2_zfmisc_1(o_0_0_xboole_0,esk8_0)
    | esk5_0 != o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( k2_zfmisc_1(o_0_0_xboole_0,esk8_0) = k2_zfmisc_1(o_0_0_xboole_0,esk4_0)
    | esk6_0 != o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( k2_zfmisc_1(o_0_0_xboole_0,esk8_0) = k2_zfmisc_1(o_0_0_xboole_0,esk4_0)
    | esk7_0 != o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_51])).

fof(c_0_57,plain,(
    ! [X36,X37,X38,X39,X40,X41] :
      ( ( X36 = X39
        | X36 = k1_xboole_0
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0
        | k3_zfmisc_1(X36,X37,X38) != k3_zfmisc_1(X39,X40,X41) )
      & ( X37 = X40
        | X36 = k1_xboole_0
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0
        | k3_zfmisc_1(X36,X37,X38) != k3_zfmisc_1(X39,X40,X41) )
      & ( X38 = X41
        | X36 = k1_xboole_0
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0
        | k3_zfmisc_1(X36,X37,X38) != k3_zfmisc_1(X39,X40,X41) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_mcart_1])])])).

cnf(c_0_58,negated_conjecture,
    ( k2_zfmisc_1(k3_zfmisc_1(esk5_0,esk6_0,esk7_0),esk4_0) = k2_zfmisc_1(k3_zfmisc_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[c_0_21,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = o_0_0_xboole_0
    | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = X1
    | k2_zfmisc_1(o_0_0_xboole_0,esk8_0) != k2_zfmisc_1(X1,X2)
    | esk5_0 != o_0_0_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_27])).

cnf(c_0_60,negated_conjecture,
    ( X1 = o_0_0_xboole_0
    | X2 = o_0_0_xboole_0
    | k2_zfmisc_1(X2,X1) != k2_zfmisc_1(o_0_0_xboole_0,esk4_0)
    | esk6_0 != o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( X1 = o_0_0_xboole_0
    | X2 = o_0_0_xboole_0
    | k2_zfmisc_1(X2,X1) != k2_zfmisc_1(o_0_0_xboole_0,esk4_0)
    | esk7_0 != o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_56])).

cnf(c_0_62,plain,
    ( X1 = X2
    | X1 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | k3_zfmisc_1(X1,X3,X4) != k3_zfmisc_1(X2,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( k3_zfmisc_1(esk5_0,esk6_0,esk7_0) = o_0_0_xboole_0
    | k3_zfmisc_1(esk5_0,esk6_0,esk7_0) = X1
    | k2_zfmisc_1(k3_zfmisc_1(esk1_0,esk2_0,esk3_0),esk4_0) != k2_zfmisc_1(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_58]),c_0_27])).

cnf(c_0_64,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = o_0_0_xboole_0
    | esk5_0 != o_0_0_xboole_0 ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = o_0_0_xboole_0
    | esk6_0 != o_0_0_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_50]),c_0_27])).

cnf(c_0_66,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = o_0_0_xboole_0
    | esk7_0 != o_0_0_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_51]),c_0_27])).

cnf(c_0_67,plain,
    ( X1 = o_0_0_xboole_0
    | X2 = o_0_0_xboole_0
    | X3 = o_0_0_xboole_0
    | X1 = X4
    | k3_zfmisc_1(X1,X2,X3) != k3_zfmisc_1(X4,X5,X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_68,negated_conjecture,
    ( k3_zfmisc_1(esk5_0,esk6_0,esk7_0) = k3_zfmisc_1(esk1_0,esk2_0,esk3_0)
    | k3_zfmisc_1(esk5_0,esk6_0,esk7_0) = o_0_0_xboole_0 ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( esk5_0 != o_0_0_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_64]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_70,negated_conjecture,
    ( esk6_0 != o_0_0_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_65]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_71,negated_conjecture,
    ( esk7_0 != o_0_0_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_66]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_72,negated_conjecture,
    ( k3_zfmisc_1(esk5_0,esk6_0,esk7_0) = o_0_0_xboole_0
    | esk5_0 = X1
    | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k3_zfmisc_1(X1,X2,X3) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69]),c_0_70]),c_0_71])).

cnf(c_0_73,negated_conjecture,
    ( k3_zfmisc_1(esk5_0,esk6_0,esk7_0) = o_0_0_xboole_0
    | esk5_0 = esk1_0 ),
    inference(er,[status(thm)],[c_0_72])).

cnf(c_0_74,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X1 = k1_xboole_0
    | k3_zfmisc_1(X3,X4,X1) != k3_zfmisc_1(X5,X6,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_75,negated_conjecture,
    ( esk5_0 = esk1_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_73]),c_0_69]),c_0_70]),c_0_71])).

cnf(c_0_76,plain,
    ( X1 = o_0_0_xboole_0
    | X2 = o_0_0_xboole_0
    | X3 = o_0_0_xboole_0
    | X1 = X4
    | k3_zfmisc_1(X2,X3,X1) != k3_zfmisc_1(X5,X6,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_77,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk6_0,esk7_0) = k3_zfmisc_1(esk1_0,esk2_0,esk3_0)
    | k3_zfmisc_1(esk1_0,esk6_0,esk7_0) = o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_75]),c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk6_0,esk7_0) = o_0_0_xboole_0
    | esk7_0 = X1
    | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k3_zfmisc_1(X2,X3,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_71]),c_0_37]),c_0_70])).

cnf(c_0_79,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk6_0,esk7_0) = o_0_0_xboole_0
    | esk7_0 = esk3_0 ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_80,negated_conjecture,
    ( esk1_0 != esk5_0
    | esk2_0 != esk6_0
    | esk3_0 != esk7_0
    | esk4_0 != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_81,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k1_xboole_0
    | k3_zfmisc_1(X3,X1,X4) != k3_zfmisc_1(X5,X2,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_82,negated_conjecture,
    ( esk7_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_79]),c_0_37]),c_0_70]),c_0_71])).

cnf(c_0_83,negated_conjecture,
    ( esk5_0 != esk1_0
    | esk6_0 != esk2_0
    | esk7_0 != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_52])])).

cnf(c_0_84,plain,
    ( X1 = o_0_0_xboole_0
    | X2 = o_0_0_xboole_0
    | X3 = o_0_0_xboole_0
    | X1 = X4
    | k3_zfmisc_1(X2,X1,X3) != k3_zfmisc_1(X5,X4,X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_85,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk6_0,esk3_0) = k3_zfmisc_1(esk1_0,esk2_0,esk3_0)
    | k3_zfmisc_1(esk1_0,esk6_0,esk3_0) = o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_82]),c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( esk6_0 != esk2_0
    | esk7_0 != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_75])])).

cnf(c_0_87,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk6_0,esk3_0) = o_0_0_xboole_0
    | esk6_0 = X1
    | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k3_zfmisc_1(X2,X1,X3) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_70]),c_0_37]),c_0_39])).

cnf(c_0_88,negated_conjecture,
    ( esk6_0 != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_82])])).

cnf(c_0_89,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk6_0,esk3_0) = o_0_0_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_87]),c_0_88])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_89]),c_0_37]),c_0_70]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
