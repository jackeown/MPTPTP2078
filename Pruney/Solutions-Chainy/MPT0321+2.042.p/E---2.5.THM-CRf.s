%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:03 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 950 expanded)
%              Number of clauses        :   61 ( 466 expanded)
%              Number of leaves         :   10 ( 241 expanded)
%              Depth                    :   20
%              Number of atoms          :  217 (3153 expanded)
%              Number of equality atoms :   46 ( 794 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t6_xboole_0,axiom,(
    ! [X1,X2] :
      ~ ( r2_xboole_0(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ~ r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t134_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(c_0_10,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22] :
      ( ( r2_hidden(X18,X15)
        | ~ r2_hidden(X18,X17)
        | X17 != k3_xboole_0(X15,X16) )
      & ( r2_hidden(X18,X16)
        | ~ r2_hidden(X18,X17)
        | X17 != k3_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X19,X15)
        | ~ r2_hidden(X19,X16)
        | r2_hidden(X19,X17)
        | X17 != k3_xboole_0(X15,X16) )
      & ( ~ r2_hidden(esk3_3(X20,X21,X22),X22)
        | ~ r2_hidden(esk3_3(X20,X21,X22),X20)
        | ~ r2_hidden(esk3_3(X20,X21,X22),X21)
        | X22 = k3_xboole_0(X20,X21) )
      & ( r2_hidden(esk3_3(X20,X21,X22),X20)
        | r2_hidden(esk3_3(X20,X21,X22),X22)
        | X22 = k3_xboole_0(X20,X21) )
      & ( r2_hidden(esk3_3(X20,X21,X22),X21)
        | r2_hidden(esk3_3(X20,X21,X22),X22)
        | X22 = k3_xboole_0(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_11,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_12,plain,(
    ! [X29,X30] :
      ( ( r2_hidden(esk5_2(X29,X30),X30)
        | ~ r2_xboole_0(X29,X30) )
      & ( ~ r2_hidden(esk5_2(X29,X30),X29)
        | ~ r2_xboole_0(X29,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_xboole_0])])])])])).

fof(c_0_13,plain,(
    ! [X24,X25] :
      ( ( r1_tarski(X24,X25)
        | ~ r2_xboole_0(X24,X25) )
      & ( X24 != X25
        | ~ r2_xboole_0(X24,X25) )
      & ( ~ r1_tarski(X24,X25)
        | X24 = X25
        | r2_xboole_0(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

fof(c_0_14,plain,(
    ! [X32] : r1_tarski(k1_xboole_0,X32) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(esk5_2(X1,X2),X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( ~ r2_xboole_0(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( k1_xboole_0 = X1
    | r2_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_1(k3_xboole_0(X1,X2)),X2)
    | v1_xboole_0(k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | ( X1 = X3
            & X2 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t134_zfmisc_1])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,plain,
    ( k1_xboole_0 = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( v1_xboole_0(k3_xboole_0(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_24])).

fof(c_0_29,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_30,plain,(
    ! [X33,X34,X35,X36] :
      ( ( r2_hidden(X33,X35)
        | ~ r2_hidden(k4_tarski(X33,X34),k2_zfmisc_1(X35,X36)) )
      & ( r2_hidden(X34,X36)
        | ~ r2_hidden(k4_tarski(X33,X34),k2_zfmisc_1(X35,X36)) )
      & ( ~ r2_hidden(X33,X35)
        | ~ r2_hidden(X34,X36)
        | r2_hidden(k4_tarski(X33,X34),k2_zfmisc_1(X35,X36)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

fof(c_0_31,negated_conjecture,
    ( k2_zfmisc_1(esk6_0,esk7_0) = k2_zfmisc_1(esk8_0,esk9_0)
    & esk6_0 != k1_xboole_0
    & esk7_0 != k1_xboole_0
    & ( esk6_0 != esk8_0
      | esk7_0 != esk9_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_35,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( k2_zfmisc_1(esk6_0,esk7_0) = k2_zfmisc_1(esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ v1_xboole_0(k3_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_32])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_19])).

fof(c_0_41,plain,(
    ! [X26,X27] :
      ( ( ~ r2_hidden(esk4_2(X26,X27),X26)
        | ~ r2_hidden(esk4_2(X26,X27),X27)
        | X26 = X27 )
      & ( r2_hidden(esk4_2(X26,X27),X26)
        | r2_hidden(esk4_2(X26,X27),X27)
        | X26 = X27 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_34])]),c_0_40])).

cnf(c_0_46,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r2_hidden(esk4_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X2,esk6_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_2(X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X2,esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_44])).

cnf(c_0_52,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk4_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk6_0,esk7_0))
    | ~ r2_hidden(X2,esk9_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_37])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,k1_xboole_0),esk9_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X2,esk9_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,k1_xboole_0),esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_52]),c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(X1,esk8_0)
    | ~ r2_hidden(esk2_2(X1,esk8_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(esk6_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,plain,
    ( ~ r2_hidden(esk5_2(X1,X2),X1)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk5_2(X1,esk8_0),esk6_0)
    | ~ r2_xboole_0(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_17])).

cnf(c_0_66,negated_conjecture,
    ( esk8_0 = esk6_0
    | r2_xboole_0(esk6_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( ~ r2_xboole_0(esk6_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(esk7_0,X1)
    | r2_hidden(esk2_2(esk7_0,X1),esk9_0)
    | ~ r2_hidden(X2,esk6_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X2,esk8_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_53])).

cnf(c_0_70,negated_conjecture,
    ( esk8_0 = esk6_0 ),
    inference(sr,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(esk7_0,X1)
    | r2_hidden(esk2_2(esk7_0,X1),esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_52]),c_0_55])).

cnf(c_0_72,negated_conjecture,
    ( esk6_0 != esk8_0
    | esk7_0 != esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X2,esk6_0) ),
    inference(rw,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(esk7_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( esk9_0 != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_70])])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk5_2(X1,esk9_0),esk7_0)
    | ~ r2_xboole_0(X1,esk9_0)
    | ~ r2_hidden(X2,esk6_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_17])).

cnf(c_0_77,negated_conjecture,
    ( r2_xboole_0(esk7_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_74]),c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk5_2(esk7_0,esk9_0),esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk5_2(esk7_0,esk9_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_52]),c_0_55])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_79]),c_0_77])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:38:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.43  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.028 s
% 0.20/0.43  # Presaturation interreduction done
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.20/0.43  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.43  fof(t6_xboole_0, axiom, ![X1, X2]:~((r2_xboole_0(X1,X2)&![X3]:~((r2_hidden(X3,X2)&~(r2_hidden(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 0.20/0.43  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.20/0.43  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.43  fof(t134_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 0.20/0.43  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.43  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.20/0.43  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.43  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 0.20/0.43  fof(c_0_10, plain, ![X15, X16, X17, X18, X19, X20, X21, X22]:((((r2_hidden(X18,X15)|~r2_hidden(X18,X17)|X17!=k3_xboole_0(X15,X16))&(r2_hidden(X18,X16)|~r2_hidden(X18,X17)|X17!=k3_xboole_0(X15,X16)))&(~r2_hidden(X19,X15)|~r2_hidden(X19,X16)|r2_hidden(X19,X17)|X17!=k3_xboole_0(X15,X16)))&((~r2_hidden(esk3_3(X20,X21,X22),X22)|(~r2_hidden(esk3_3(X20,X21,X22),X20)|~r2_hidden(esk3_3(X20,X21,X22),X21))|X22=k3_xboole_0(X20,X21))&((r2_hidden(esk3_3(X20,X21,X22),X20)|r2_hidden(esk3_3(X20,X21,X22),X22)|X22=k3_xboole_0(X20,X21))&(r2_hidden(esk3_3(X20,X21,X22),X21)|r2_hidden(esk3_3(X20,X21,X22),X22)|X22=k3_xboole_0(X20,X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.20/0.43  fof(c_0_11, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.43  fof(c_0_12, plain, ![X29, X30]:((r2_hidden(esk5_2(X29,X30),X30)|~r2_xboole_0(X29,X30))&(~r2_hidden(esk5_2(X29,X30),X29)|~r2_xboole_0(X29,X30))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_xboole_0])])])])])).
% 0.20/0.43  fof(c_0_13, plain, ![X24, X25]:(((r1_tarski(X24,X25)|~r2_xboole_0(X24,X25))&(X24!=X25|~r2_xboole_0(X24,X25)))&(~r1_tarski(X24,X25)|X24=X25|r2_xboole_0(X24,X25))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.20/0.43  fof(c_0_14, plain, ![X32]:r1_tarski(k1_xboole_0,X32), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.43  cnf(c_0_15, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.43  cnf(c_0_16, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_17, plain, (r2_hidden(esk5_2(X1,X2),X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.43  cnf(c_0_18, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.43  cnf(c_0_19, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.43  cnf(c_0_20, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_15])).
% 0.20/0.43  cnf(c_0_21, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_22, plain, (~r2_xboole_0(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.43  cnf(c_0_23, plain, (k1_xboole_0=X1|r2_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.43  cnf(c_0_24, plain, (r2_hidden(esk1_1(k3_xboole_0(X1,X2)),X2)|v1_xboole_0(k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.43  fof(c_0_25, negated_conjecture, ~(![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4)))), inference(assume_negation,[status(cth)],[t134_zfmisc_1])).
% 0.20/0.43  cnf(c_0_26, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.43  cnf(c_0_27, plain, (k1_xboole_0=X1|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.43  cnf(c_0_28, plain, (v1_xboole_0(k3_xboole_0(X1,X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_16, c_0_24])).
% 0.20/0.43  fof(c_0_29, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.43  fof(c_0_30, plain, ![X33, X34, X35, X36]:(((r2_hidden(X33,X35)|~r2_hidden(k4_tarski(X33,X34),k2_zfmisc_1(X35,X36)))&(r2_hidden(X34,X36)|~r2_hidden(k4_tarski(X33,X34),k2_zfmisc_1(X35,X36))))&(~r2_hidden(X33,X35)|~r2_hidden(X34,X36)|r2_hidden(k4_tarski(X33,X34),k2_zfmisc_1(X35,X36)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.20/0.43  fof(c_0_31, negated_conjecture, (k2_zfmisc_1(esk6_0,esk7_0)=k2_zfmisc_1(esk8_0,esk9_0)&((esk6_0!=k1_xboole_0&esk7_0!=k1_xboole_0)&(esk6_0!=esk8_0|esk7_0!=esk9_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.20/0.43  cnf(c_0_32, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_26])).
% 0.20/0.43  cnf(c_0_33, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.43  cnf(c_0_34, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.43  cnf(c_0_35, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.43  cnf(c_0_36, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.43  cnf(c_0_37, negated_conjecture, (k2_zfmisc_1(esk6_0,esk7_0)=k2_zfmisc_1(esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.43  cnf(c_0_38, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~v1_xboole_0(k3_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_16, c_0_32])).
% 0.20/0.43  cnf(c_0_39, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.43  cnf(c_0_40, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_35, c_0_19])).
% 0.20/0.43  fof(c_0_41, plain, ![X26, X27]:((~r2_hidden(esk4_2(X26,X27),X26)|~r2_hidden(esk4_2(X26,X27),X27)|X26=X27)&(r2_hidden(esk4_2(X26,X27),X26)|r2_hidden(esk4_2(X26,X27),X27)|X26=X27)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.20/0.43  cnf(c_0_42, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.43  cnf(c_0_43, negated_conjecture, (r2_hidden(X1,esk9_0)|~r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.43  cnf(c_0_44, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.43  cnf(c_0_45, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_34])]), c_0_40])).
% 0.20/0.43  cnf(c_0_46, plain, (r2_hidden(esk4_2(X1,X2),X1)|r2_hidden(esk4_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.43  cnf(c_0_47, negated_conjecture, (r2_hidden(X1,esk8_0)|~r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_42, c_0_37])).
% 0.20/0.43  cnf(c_0_48, negated_conjecture, (r2_hidden(X1,esk9_0)|~r2_hidden(X1,esk7_0)|~r2_hidden(X2,esk6_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.43  cnf(c_0_49, plain, (X1=k1_xboole_0|r2_hidden(esk4_2(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.43  cnf(c_0_50, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.43  cnf(c_0_51, negated_conjecture, (r2_hidden(X1,esk8_0)|~r2_hidden(X2,esk7_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_47, c_0_44])).
% 0.20/0.43  cnf(c_0_52, plain, (k1_xboole_0=X1|r2_hidden(esk4_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.43  cnf(c_0_53, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk6_0,esk7_0))|~r2_hidden(X2,esk9_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_44, c_0_37])).
% 0.20/0.43  cnf(c_0_54, negated_conjecture, (r2_hidden(esk4_2(esk7_0,k1_xboole_0),esk9_0)|~r2_hidden(X1,esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])).
% 0.20/0.43  cnf(c_0_55, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.43  cnf(c_0_56, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.43  cnf(c_0_57, negated_conjecture, (r2_hidden(X1,esk8_0)|~r2_hidden(X1,esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_50])).
% 0.20/0.43  cnf(c_0_58, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X2,esk9_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_42, c_0_53])).
% 0.20/0.43  cnf(c_0_59, negated_conjecture, (r2_hidden(esk4_2(esk7_0,k1_xboole_0),esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_52]), c_0_55])).
% 0.20/0.43  cnf(c_0_60, negated_conjecture, (r1_tarski(X1,esk8_0)|~r2_hidden(esk2_2(X1,esk8_0),esk6_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.43  cnf(c_0_61, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.43  cnf(c_0_62, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.20/0.43  cnf(c_0_63, negated_conjecture, (r1_tarski(esk6_0,esk8_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.43  cnf(c_0_64, plain, (~r2_hidden(esk5_2(X1,X2),X1)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.43  cnf(c_0_65, negated_conjecture, (r2_hidden(esk5_2(X1,esk8_0),esk6_0)|~r2_xboole_0(X1,esk8_0)), inference(spm,[status(thm)],[c_0_62, c_0_17])).
% 0.20/0.43  cnf(c_0_66, negated_conjecture, (esk8_0=esk6_0|r2_xboole_0(esk6_0,esk8_0)), inference(spm,[status(thm)],[c_0_18, c_0_63])).
% 0.20/0.43  cnf(c_0_67, negated_conjecture, (~r2_xboole_0(esk6_0,esk8_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.20/0.43  cnf(c_0_68, negated_conjecture, (r1_tarski(esk7_0,X1)|r2_hidden(esk2_2(esk7_0,X1),esk9_0)|~r2_hidden(X2,esk6_0)), inference(spm,[status(thm)],[c_0_48, c_0_61])).
% 0.20/0.43  cnf(c_0_69, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk9_0)|~r2_hidden(X2,esk8_0)), inference(spm,[status(thm)],[c_0_36, c_0_53])).
% 0.20/0.43  cnf(c_0_70, negated_conjecture, (esk8_0=esk6_0), inference(sr,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.43  cnf(c_0_71, negated_conjecture, (r1_tarski(esk7_0,X1)|r2_hidden(esk2_2(esk7_0,X1),esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_52]), c_0_55])).
% 0.20/0.43  cnf(c_0_72, negated_conjecture, (esk6_0!=esk8_0|esk7_0!=esk9_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.43  cnf(c_0_73, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk9_0)|~r2_hidden(X2,esk6_0)), inference(rw,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.43  cnf(c_0_74, negated_conjecture, (r1_tarski(esk7_0,esk9_0)), inference(spm,[status(thm)],[c_0_56, c_0_71])).
% 0.20/0.43  cnf(c_0_75, negated_conjecture, (esk9_0!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_70])])).
% 0.20/0.43  cnf(c_0_76, negated_conjecture, (r2_hidden(esk5_2(X1,esk9_0),esk7_0)|~r2_xboole_0(X1,esk9_0)|~r2_hidden(X2,esk6_0)), inference(spm,[status(thm)],[c_0_73, c_0_17])).
% 0.20/0.43  cnf(c_0_77, negated_conjecture, (r2_xboole_0(esk7_0,esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_74]), c_0_75])).
% 0.20/0.43  cnf(c_0_78, negated_conjecture, (r2_hidden(esk5_2(esk7_0,esk9_0),esk7_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.20/0.43  cnf(c_0_79, negated_conjecture, (r2_hidden(esk5_2(esk7_0,esk9_0),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_52]), c_0_55])).
% 0.20/0.43  cnf(c_0_80, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_79]), c_0_77])]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 81
% 0.20/0.43  # Proof object clause steps            : 61
% 0.20/0.43  # Proof object formula steps           : 20
% 0.20/0.43  # Proof object conjectures             : 34
% 0.20/0.43  # Proof object clause conjectures      : 31
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 20
% 0.20/0.43  # Proof object initial formulas used   : 10
% 0.20/0.43  # Proof object generating inferences   : 36
% 0.20/0.43  # Proof object simplifying inferences  : 17
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 10
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 27
% 0.20/0.43  # Removed in clause preprocessing      : 0
% 0.20/0.43  # Initial clauses in saturation        : 27
% 0.20/0.43  # Processed clauses                    : 705
% 0.20/0.43  # ...of these trivial                  : 1
% 0.20/0.43  # ...subsumed                          : 403
% 0.20/0.43  # ...remaining for further processing  : 301
% 0.20/0.43  # Other redundant clauses eliminated   : 4
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 35
% 0.20/0.43  # Backward-rewritten                   : 75
% 0.20/0.43  # Generated clauses                    : 3141
% 0.20/0.43  # ...of the previous two non-trivial   : 2997
% 0.20/0.43  # Contextual simplify-reflections      : 3
% 0.20/0.43  # Paramodulations                      : 3097
% 0.20/0.43  # Factorizations                       : 38
% 0.20/0.43  # Equation resolutions                 : 4
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
% 0.20/0.43  # Current number of processed clauses  : 158
% 0.20/0.43  #    Positive orientable unit clauses  : 29
% 0.20/0.43  #    Positive unorientable unit clauses: 0
% 0.20/0.43  #    Negative unit clauses             : 16
% 0.20/0.43  #    Non-unit-clauses                  : 113
% 0.20/0.43  # Current number of unprocessed clauses: 2017
% 0.20/0.43  # ...number of literals in the above   : 6985
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 139
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 5636
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 4309
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 158
% 0.20/0.43  # Unit Clause-clause subsumption calls : 934
% 0.20/0.43  # Rewrite failures with RHS unbound    : 0
% 0.20/0.43  # BW rewrite match attempts            : 23
% 0.20/0.43  # BW rewrite match successes           : 15
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 38818
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.079 s
% 0.20/0.43  # System time              : 0.007 s
% 0.20/0.43  # Total time               : 0.087 s
% 0.20/0.43  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
