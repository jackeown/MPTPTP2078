%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:02 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  104 (12218 expanded)
%              Number of clauses        :   89 (6137 expanded)
%              Number of leaves         :    7 (2882 expanded)
%              Depth                    :   26
%              Number of atoms          :  243 (60060 expanded)
%              Number of equality atoms :  119 (21953 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(t134_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t117_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))
          | r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) )
        & ~ r1_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_7,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | ( X1 = X3
            & X2 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t134_zfmisc_1])).

cnf(c_0_9,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X27,X28,X29,X30] : k2_zfmisc_1(k3_xboole_0(X27,X28),k3_xboole_0(X29,X30)) = k3_xboole_0(k2_zfmisc_1(X27,X29),k2_zfmisc_1(X28,X30)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

fof(c_0_11,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k2_zfmisc_1(esk5_0,esk6_0)
    & esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & ( esk3_0 != esk5_0
      | esk4_0 != esk6_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_12,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k2_zfmisc_1(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r2_hidden(esk2_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_18,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_19,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(X1,esk5_0),k3_xboole_0(X2,esk6_0)) = k2_zfmisc_1(k3_xboole_0(X1,esk3_0),k3_xboole_0(X2,esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_14])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_16,c_0_13])).

fof(c_0_21,plain,(
    ! [X22,X23] :
      ( ~ r1_tarski(X22,X23)
      | k3_xboole_0(X22,X23) = X22 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk5_0,esk3_0),k3_xboole_0(X1,esk4_0)) = k2_zfmisc_1(esk5_0,k3_xboole_0(X1,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_2(k3_xboole_0(X1,X2),X3),X2)
    | r1_tarski(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk5_0,X1),k3_xboole_0(esk6_0,X2)) = k2_zfmisc_1(k3_xboole_0(esk3_0,X1),k3_xboole_0(esk4_0,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_14])).

cnf(c_0_31,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(X1,esk3_0),k3_xboole_0(esk6_0,esk4_0)) = k2_zfmisc_1(k3_xboole_0(X1,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk5_0,esk3_0),X1) = k2_zfmisc_1(esk5_0,k3_xboole_0(X1,esk6_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_2(k3_xboole_0(X1,X2),X3),X1)
    | r1_tarski(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_29,c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),k3_xboole_0(esk4_0,X1)) = k2_zfmisc_1(esk5_0,k3_xboole_0(esk6_0,X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_20])).

cnf(c_0_36,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,k3_xboole_0(k3_xboole_0(esk6_0,esk4_0),esk6_0)) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_20]),c_0_15]),c_0_33])])).

cnf(c_0_37,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_34])).

fof(c_0_38,plain,(
    ! [X24,X25,X26] :
      ( ( ~ r1_tarski(k2_zfmisc_1(X25,X24),k2_zfmisc_1(X26,X24))
        | X24 = k1_xboole_0
        | r1_tarski(X25,X26) )
      & ( ~ r1_tarski(k2_zfmisc_1(X24,X25),k2_zfmisc_1(X24,X26))
        | X24 = k1_xboole_0
        | r1_tarski(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).

fof(c_0_39,plain,(
    ! [X20,X21] :
      ( ( r1_tarski(X20,X21)
        | X20 != X21 )
      & ( r1_tarski(X21,X20)
        | X20 != X21 )
      & ( ~ r1_tarski(X20,X21)
        | ~ r1_tarski(X21,X20)
        | X20 = X21 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_40,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),esk4_0) = k2_zfmisc_1(esk5_0,k3_xboole_0(esk6_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_20])).

cnf(c_0_41,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,k3_xboole_0(esk6_0,esk4_0)) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_26]),c_0_37])])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),esk4_0) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_47,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk3_0,X1),k3_xboole_0(esk4_0,esk6_0)) = k2_zfmisc_1(k3_xboole_0(esk5_0,X1),esk6_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_20])).

cnf(c_0_48,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk3_0,X1),k3_xboole_0(esk4_0,X2)) = k2_zfmisc_1(k3_xboole_0(esk5_0,X1),esk6_0)
    | ~ r1_tarski(esk6_0,X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_26])).

cnf(c_0_49,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(esk6_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_15])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(X1,k3_xboole_0(esk3_0,esk5_0))
    | ~ r1_tarski(k2_zfmisc_1(X1,esk4_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(esk5_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(X1,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_15])).

cnf(c_0_53,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk5_0,esk3_0),esk6_0) = k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_20])).

cnf(c_0_54,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk5_0,X1),esk6_0) = k2_zfmisc_1(k3_xboole_0(esk3_0,X1),esk4_0)
    | ~ r1_tarski(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_20])).

cnf(c_0_55,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_56,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(esk6_0,k3_xboole_0(esk6_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_41]),c_0_50])])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(esk3_0,k3_xboole_0(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(esk5_0,k3_xboole_0(esk5_0,esk3_0))
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,esk6_0)) = k2_zfmisc_1(esk3_0,esk4_0)
    | ~ r1_tarski(esk6_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_20])).

cnf(c_0_60,negated_conjecture,
    ( k3_xboole_0(esk6_0,esk4_0) = esk6_0
    | esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_37])])).

cnf(c_0_61,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_57]),c_0_37])])).

cnf(c_0_62,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk5_0,X1),esk6_0) = k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,esk6_0))
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_26])).

cnf(c_0_63,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(esk5_0,k3_xboole_0(esk5_0,esk3_0))
    | ~ r1_tarski(esk6_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_50])])).

cnf(c_0_64,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,esk6_0)) = k2_zfmisc_1(esk3_0,esk4_0)
    | ~ r1_tarski(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_20]),c_0_15])).

cnf(c_0_67,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | r1_tarski(esk5_0,k3_xboole_0(esk5_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( k3_xboole_0(esk5_0,X1) = X1
    | ~ r2_hidden(esk2_3(esk5_0,X1,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(esk5_0,k3_xboole_0(esk5_0,esk3_0))
    | ~ r1_tarski(esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_66]),c_0_50])])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_61])).

cnf(c_0_71,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk5_0,esk3_0),esk4_0) = k2_zfmisc_1(esk5_0,k3_xboole_0(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_20])).

cnf(c_0_72,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk3_0) = esk5_0
    | esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_67]),c_0_37])])).

cnf(c_0_73,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_13])).

cnf(c_0_74,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(esk5_0,k3_xboole_0(esk5_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70])])).

cnf(c_0_75,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,k3_xboole_0(esk4_0,esk6_0)) = k2_zfmisc_1(esk5_0,esk4_0)
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,k3_xboole_0(esk4_0,esk6_0)) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_71,c_0_73])).

cnf(c_0_77,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_33])).

cnf(c_0_78,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk3_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_74]),c_0_37])])).

cnf(c_0_79,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k2_zfmisc_1(X1,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_14])).

cnf(c_0_80,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(X1,esk6_0)
    | ~ r1_tarski(k2_zfmisc_1(esk5_0,X1),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_15])).

cnf(c_0_81,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk4_0) = k2_zfmisc_1(esk3_0,esk4_0)
    | esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( esk3_0 != esk5_0
    | esk4_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_83,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_70])])).

cnf(c_0_84,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk5_0,X1),esk6_0) = k2_zfmisc_1(esk3_0,esk4_0)
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(X1,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_79])).

cnf(c_0_85,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk6_0 = esk4_0
    | ~ r1_tarski(esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_60])).

cnf(c_0_86,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | r1_tarski(esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_50])])).

cnf(c_0_87,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk6_0 != esk4_0 ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_88,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk3_0)),esk6_0) = k2_zfmisc_1(esk3_0,esk4_0)
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_53])).

cnf(c_0_89,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87])).

cnf(c_0_90,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_91,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk3_0)),esk6_0) = k2_zfmisc_1(esk3_0,esk4_0)
    | ~ r1_tarski(esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_66]),c_0_50])])).

cnf(c_0_92,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_89]),c_0_90])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(k2_zfmisc_1(X1,esk4_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_51,c_0_61])).

cnf(c_0_94,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk4_0) = k2_zfmisc_1(esk3_0,esk4_0)
    | ~ r1_tarski(esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_26])).

cnf(c_0_95,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k2_zfmisc_1(esk3_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_70])]),c_0_73]),c_0_73]),c_0_92])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(esk5_0,esk3_0)
    | ~ r1_tarski(esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_50])])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,k1_xboole_0),k2_zfmisc_1(esk3_0,X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_95]),c_0_90])).

cnf(c_0_98,negated_conjecture,
    ( esk5_0 = esk3_0
    | ~ r1_tarski(esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_96]),c_0_70])])).

cnf(c_0_99,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_92]),c_0_92]),c_0_46])).

cnf(c_0_100,negated_conjecture,
    ( r1_tarski(esk4_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_50])).

cnf(c_0_101,negated_conjecture,
    ( esk5_0 = esk3_0
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_98,c_0_92])).

cnf(c_0_102,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_100])])).

cnf(c_0_103,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_100])]),c_0_102]),c_0_90]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:34:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.014 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.20/0.39  fof(t134_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 0.20/0.39  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 0.20/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.39  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.39  fof(t117_zfmisc_1, axiom, ![X1, X2, X3]:~(((X1!=k1_xboole_0&(r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))|r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))))&~(r1_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 0.20/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.39  fof(c_0_7, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12))&(r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k3_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k3_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))&(r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.20/0.39  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4)))), inference(assume_negation,[status(cth)],[t134_zfmisc_1])).
% 0.20/0.39  cnf(c_0_9, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  fof(c_0_10, plain, ![X27, X28, X29, X30]:k2_zfmisc_1(k3_xboole_0(X27,X28),k3_xboole_0(X29,X30))=k3_xboole_0(k2_zfmisc_1(X27,X29),k2_zfmisc_1(X28,X30)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 0.20/0.39  fof(c_0_11, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k2_zfmisc_1(esk5_0,esk6_0)&((esk3_0!=k1_xboole_0&esk4_0!=k1_xboole_0)&(esk3_0!=esk5_0|esk4_0!=esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.20/0.39  cnf(c_0_12, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  cnf(c_0_13, plain, (k3_xboole_0(X1,X2)=X2|r2_hidden(esk2_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_14, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_15, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k2_zfmisc_1(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_16, plain, (k3_xboole_0(X1,X2)=X2|~r2_hidden(esk2_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_13])).
% 0.20/0.39  cnf(c_0_17, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  fof(c_0_18, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.39  cnf(c_0_19, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(X1,esk5_0),k3_xboole_0(X2,esk6_0))=k2_zfmisc_1(k3_xboole_0(X1,esk3_0),k3_xboole_0(X2,esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_14])).
% 0.20/0.39  cnf(c_0_20, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_16, c_0_13])).
% 0.20/0.39  fof(c_0_21, plain, ![X22, X23]:(~r1_tarski(X22,X23)|k3_xboole_0(X22,X23)=X22), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.39  cnf(c_0_22, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_23, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_24, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  cnf(c_0_25, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk5_0,esk3_0),k3_xboole_0(X1,esk4_0))=k2_zfmisc_1(esk5_0,k3_xboole_0(X1,esk6_0))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.39  cnf(c_0_26, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.39  cnf(c_0_27, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_28, plain, (r2_hidden(esk1_2(k3_xboole_0(X1,X2),X3),X2)|r1_tarski(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.39  cnf(c_0_29, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_24])).
% 0.20/0.39  cnf(c_0_30, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk5_0,X1),k3_xboole_0(esk6_0,X2))=k2_zfmisc_1(k3_xboole_0(esk3_0,X1),k3_xboole_0(esk4_0,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_14])).
% 0.20/0.39  cnf(c_0_31, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(X1,esk3_0),k3_xboole_0(esk6_0,esk4_0))=k2_zfmisc_1(k3_xboole_0(X1,esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.39  cnf(c_0_32, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk5_0,esk3_0),X1)=k2_zfmisc_1(esk5_0,k3_xboole_0(X1,esk6_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.39  cnf(c_0_33, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.39  cnf(c_0_34, plain, (r2_hidden(esk1_2(k3_xboole_0(X1,X2),X3),X1)|r1_tarski(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_29, c_0_23])).
% 0.20/0.39  cnf(c_0_35, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),k3_xboole_0(esk4_0,X1))=k2_zfmisc_1(esk5_0,k3_xboole_0(esk6_0,X1))), inference(spm,[status(thm)],[c_0_30, c_0_20])).
% 0.20/0.39  cnf(c_0_36, negated_conjecture, (k2_zfmisc_1(esk5_0,k3_xboole_0(k3_xboole_0(esk6_0,esk4_0),esk6_0))=k2_zfmisc_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_20]), c_0_15]), c_0_33])])).
% 0.20/0.39  cnf(c_0_37, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_27, c_0_34])).
% 0.20/0.39  fof(c_0_38, plain, ![X24, X25, X26]:((~r1_tarski(k2_zfmisc_1(X25,X24),k2_zfmisc_1(X26,X24))|X24=k1_xboole_0|r1_tarski(X25,X26))&(~r1_tarski(k2_zfmisc_1(X24,X25),k2_zfmisc_1(X24,X26))|X24=k1_xboole_0|r1_tarski(X25,X26))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).
% 0.20/0.39  fof(c_0_39, plain, ![X20, X21]:(((r1_tarski(X20,X21)|X20!=X21)&(r1_tarski(X21,X20)|X20!=X21))&(~r1_tarski(X20,X21)|~r1_tarski(X21,X20)|X20=X21)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.39  cnf(c_0_40, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),esk4_0)=k2_zfmisc_1(esk5_0,k3_xboole_0(esk6_0,esk4_0))), inference(spm,[status(thm)],[c_0_35, c_0_20])).
% 0.20/0.39  cnf(c_0_41, negated_conjecture, (k2_zfmisc_1(esk5_0,k3_xboole_0(esk6_0,esk4_0))=k2_zfmisc_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_26]), c_0_37])])).
% 0.20/0.39  cnf(c_0_42, plain, (X1=k1_xboole_0|r1_tarski(X2,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.39  cnf(c_0_43, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.39  cnf(c_0_44, plain, (X2=k1_xboole_0|r1_tarski(X1,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.39  cnf(c_0_45, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),esk4_0)=k2_zfmisc_1(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.39  cnf(c_0_46, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_47, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk3_0,X1),k3_xboole_0(esk4_0,esk6_0))=k2_zfmisc_1(k3_xboole_0(esk5_0,X1),esk6_0)), inference(spm,[status(thm)],[c_0_30, c_0_20])).
% 0.20/0.39  cnf(c_0_48, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk3_0,X1),k3_xboole_0(esk4_0,X2))=k2_zfmisc_1(k3_xboole_0(esk5_0,X1),esk6_0)|~r1_tarski(esk6_0,X2)), inference(spm,[status(thm)],[c_0_30, c_0_26])).
% 0.20/0.39  cnf(c_0_49, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(esk6_0,X1)|~r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,X1))), inference(spm,[status(thm)],[c_0_42, c_0_15])).
% 0.20/0.39  cnf(c_0_50, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_43])).
% 0.20/0.39  cnf(c_0_51, negated_conjecture, (r1_tarski(X1,k3_xboole_0(esk3_0,esk5_0))|~r1_tarski(k2_zfmisc_1(X1,esk4_0),k2_zfmisc_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])).
% 0.20/0.39  cnf(c_0_52, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(esk5_0,X1)|~r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(X1,esk6_0))), inference(spm,[status(thm)],[c_0_44, c_0_15])).
% 0.20/0.39  cnf(c_0_53, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk5_0,esk3_0),esk6_0)=k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_47, c_0_20])).
% 0.20/0.39  cnf(c_0_54, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk5_0,X1),esk6_0)=k2_zfmisc_1(k3_xboole_0(esk3_0,X1),esk4_0)|~r1_tarski(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_48, c_0_20])).
% 0.20/0.39  cnf(c_0_55, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.39  cnf(c_0_56, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(esk6_0,k3_xboole_0(esk6_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_41]), c_0_50])])).
% 0.20/0.39  cnf(c_0_57, negated_conjecture, (r1_tarski(esk3_0,k3_xboole_0(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_51, c_0_50])).
% 0.20/0.39  cnf(c_0_58, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(esk5_0,k3_xboole_0(esk5_0,esk3_0))|~r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.39  cnf(c_0_59, negated_conjecture, (k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,esk6_0))=k2_zfmisc_1(esk3_0,esk4_0)|~r1_tarski(esk6_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_20])).
% 0.20/0.39  cnf(c_0_60, negated_conjecture, (k3_xboole_0(esk6_0,esk4_0)=esk6_0|esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_37])])).
% 0.20/0.39  cnf(c_0_61, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_57]), c_0_37])])).
% 0.20/0.39  cnf(c_0_62, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk5_0,X1),esk6_0)=k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,esk6_0))|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_47, c_0_26])).
% 0.20/0.39  cnf(c_0_63, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(esk5_0,k3_xboole_0(esk5_0,esk3_0))|~r1_tarski(esk6_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_50])])).
% 0.20/0.39  cnf(c_0_64, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_33, c_0_60])).
% 0.20/0.39  cnf(c_0_65, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_22, c_0_61])).
% 0.20/0.39  cnf(c_0_66, negated_conjecture, (k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,esk6_0))=k2_zfmisc_1(esk3_0,esk4_0)|~r1_tarski(esk3_0,esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_20]), c_0_15])).
% 0.20/0.39  cnf(c_0_67, negated_conjecture, (esk5_0=k1_xboole_0|esk6_0=k1_xboole_0|r1_tarski(esk5_0,k3_xboole_0(esk5_0,esk3_0))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.20/0.39  cnf(c_0_68, negated_conjecture, (k3_xboole_0(esk5_0,X1)=X1|~r2_hidden(esk2_3(esk5_0,X1,X1),esk3_0)), inference(spm,[status(thm)],[c_0_16, c_0_65])).
% 0.20/0.39  cnf(c_0_69, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(esk5_0,k3_xboole_0(esk5_0,esk3_0))|~r1_tarski(esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_66]), c_0_50])])).
% 0.20/0.39  cnf(c_0_70, negated_conjecture, (r1_tarski(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_33, c_0_61])).
% 0.20/0.39  cnf(c_0_71, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk5_0,esk3_0),esk4_0)=k2_zfmisc_1(esk5_0,k3_xboole_0(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_25, c_0_20])).
% 0.20/0.39  cnf(c_0_72, negated_conjecture, (k3_xboole_0(esk5_0,esk3_0)=esk5_0|esk6_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_67]), c_0_37])])).
% 0.20/0.39  cnf(c_0_73, negated_conjecture, (k3_xboole_0(esk5_0,esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_68, c_0_13])).
% 0.20/0.39  cnf(c_0_74, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(esk5_0,k3_xboole_0(esk5_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70])])).
% 0.20/0.39  cnf(c_0_75, negated_conjecture, (k2_zfmisc_1(esk5_0,k3_xboole_0(esk4_0,esk6_0))=k2_zfmisc_1(esk5_0,esk4_0)|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.39  cnf(c_0_76, negated_conjecture, (k2_zfmisc_1(esk5_0,k3_xboole_0(esk4_0,esk6_0))=k2_zfmisc_1(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_71, c_0_73])).
% 0.20/0.39  cnf(c_0_77, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_55, c_0_33])).
% 0.20/0.39  cnf(c_0_78, negated_conjecture, (k3_xboole_0(esk5_0,esk3_0)=esk5_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_74]), c_0_37])])).
% 0.20/0.39  cnf(c_0_79, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k2_zfmisc_1(X1,X3)|~r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(spm,[status(thm)],[c_0_26, c_0_14])).
% 0.20/0.39  cnf(c_0_80, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(X1,esk6_0)|~r1_tarski(k2_zfmisc_1(esk5_0,X1),k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_42, c_0_15])).
% 0.20/0.39  cnf(c_0_81, negated_conjecture, (k2_zfmisc_1(esk5_0,esk4_0)=k2_zfmisc_1(esk3_0,esk4_0)|esk6_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.20/0.39  cnf(c_0_82, negated_conjecture, (esk3_0!=esk5_0|esk4_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_83, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_70])])).
% 0.20/0.39  cnf(c_0_84, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk5_0,X1),esk6_0)=k2_zfmisc_1(esk3_0,esk4_0)|~r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(X1,esk6_0))), inference(spm,[status(thm)],[c_0_47, c_0_79])).
% 0.20/0.39  cnf(c_0_85, negated_conjecture, (esk5_0=k1_xboole_0|esk6_0=esk4_0|~r1_tarski(esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_77, c_0_60])).
% 0.20/0.39  cnf(c_0_86, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|r1_tarski(esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_50])])).
% 0.20/0.39  cnf(c_0_87, negated_conjecture, (esk6_0=k1_xboole_0|esk6_0!=esk4_0), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.20/0.39  cnf(c_0_88, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk3_0)),esk6_0)=k2_zfmisc_1(esk3_0,esk4_0)|~r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_84, c_0_53])).
% 0.20/0.39  cnf(c_0_89, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_87])).
% 0.20/0.39  cnf(c_0_90, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_91, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk3_0)),esk6_0)=k2_zfmisc_1(esk3_0,esk4_0)|~r1_tarski(esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_66]), c_0_50])])).
% 0.20/0.39  cnf(c_0_92, negated_conjecture, (esk6_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_89]), c_0_90])).
% 0.20/0.39  cnf(c_0_93, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(k2_zfmisc_1(X1,esk4_0),k2_zfmisc_1(esk3_0,esk4_0))), inference(rw,[status(thm)],[c_0_51, c_0_61])).
% 0.20/0.39  cnf(c_0_94, negated_conjecture, (k2_zfmisc_1(esk5_0,esk4_0)=k2_zfmisc_1(esk3_0,esk4_0)|~r1_tarski(esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_76, c_0_26])).
% 0.20/0.39  cnf(c_0_95, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k2_zfmisc_1(esk3_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_70])]), c_0_73]), c_0_73]), c_0_92])).
% 0.20/0.39  cnf(c_0_96, negated_conjecture, (r1_tarski(esk5_0,esk3_0)|~r1_tarski(esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_50])])).
% 0.20/0.39  cnf(c_0_97, negated_conjecture, (r1_tarski(esk4_0,X1)|~r1_tarski(k2_zfmisc_1(esk3_0,k1_xboole_0),k2_zfmisc_1(esk3_0,X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_95]), c_0_90])).
% 0.20/0.39  cnf(c_0_98, negated_conjecture, (esk5_0=esk3_0|~r1_tarski(esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_96]), c_0_70])])).
% 0.20/0.39  cnf(c_0_99, negated_conjecture, (esk5_0=k1_xboole_0|~r1_tarski(esk4_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_92]), c_0_92]), c_0_46])).
% 0.20/0.39  cnf(c_0_100, negated_conjecture, (r1_tarski(esk4_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_97, c_0_50])).
% 0.20/0.39  cnf(c_0_101, negated_conjecture, (esk5_0=esk3_0|~r1_tarski(esk4_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_98, c_0_92])).
% 0.20/0.39  cnf(c_0_102, negated_conjecture, (esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_100])])).
% 0.20/0.39  cnf(c_0_103, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_100])]), c_0_102]), c_0_90]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 104
% 0.20/0.39  # Proof object clause steps            : 89
% 0.20/0.39  # Proof object formula steps           : 15
% 0.20/0.39  # Proof object conjectures             : 68
% 0.20/0.39  # Proof object clause conjectures      : 65
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 16
% 0.20/0.39  # Proof object initial formulas used   : 7
% 0.20/0.39  # Proof object generating inferences   : 61
% 0.20/0.39  # Proof object simplifying inferences  : 62
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 7
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 20
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 20
% 0.20/0.39  # Processed clauses                    : 498
% 0.20/0.39  # ...of these trivial                  : 19
% 0.20/0.39  # ...subsumed                          : 187
% 0.20/0.39  # ...remaining for further processing  : 291
% 0.20/0.39  # Other redundant clauses eliminated   : 5
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 36
% 0.20/0.39  # Backward-rewritten                   : 166
% 0.20/0.39  # Generated clauses                    : 3840
% 0.20/0.39  # ...of the previous two non-trivial   : 3463
% 0.20/0.39  # Contextual simplify-reflections      : 3
% 0.20/0.39  # Paramodulations                      : 3822
% 0.20/0.39  # Factorizations                       : 13
% 0.20/0.39  # Equation resolutions                 : 5
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 65
% 0.20/0.39  #    Positive orientable unit clauses  : 11
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 2
% 0.20/0.39  #    Non-unit-clauses                  : 52
% 0.20/0.39  # Current number of unprocessed clauses: 2959
% 0.20/0.39  # ...number of literals in the above   : 9279
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 221
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 3500
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 3089
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 209
% 0.20/0.39  # Unit Clause-clause subsumption calls : 646
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 51
% 0.20/0.39  # BW rewrite match successes           : 27
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 60232
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.047 s
% 0.20/0.39  # System time              : 0.002 s
% 0.20/0.39  # Total time               : 0.049 s
% 0.20/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
