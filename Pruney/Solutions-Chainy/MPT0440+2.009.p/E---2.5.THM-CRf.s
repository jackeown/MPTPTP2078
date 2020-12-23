%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:12 EST 2020

% Result     : Theorem 0.56s
% Output     : CNFRefutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   72 (1041 expanded)
%              Number of clauses        :   55 ( 496 expanded)
%              Number of leaves         :    8 ( 253 expanded)
%              Depth                    :   22
%              Number of atoms          :  191 (2826 expanded)
%              Number of equality atoms :   89 (1835 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( X3 = k1_tarski(k4_tarski(X1,X2))
       => ( k1_relat_1(X3) = k1_tarski(X1)
          & k2_relat_1(X3) = k1_tarski(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(t129_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X4)))
    <=> ( r2_hidden(X1,X3)
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(t35_zfmisc_1,axiom,(
    ! [X1,X2] : k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(t128_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))
    <=> ( X1 = X3
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( X3 = k1_tarski(k4_tarski(X1,X2))
         => ( k1_relat_1(X3) = k1_tarski(X1)
            & k2_relat_1(X3) = k1_tarski(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_relat_1])).

fof(c_0_9,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( ~ r2_hidden(X7,X6)
        | X7 = X5
        | X6 != k1_tarski(X5) )
      & ( X8 != X5
        | r2_hidden(X8,X6)
        | X6 != k1_tarski(X5) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) != X9
        | X10 = k1_tarski(X9) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) = X9
        | X10 = k1_tarski(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_10,plain,(
    ! [X12] : k2_tarski(X12,X12) = k1_tarski(X12) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_11,negated_conjecture,
    ( v1_relat_1(esk10_0)
    & esk10_0 = k1_tarski(k4_tarski(esk8_0,esk9_0))
    & ( k1_relat_1(esk10_0) != k1_tarski(esk8_0)
      | k2_relat_1(esk10_0) != k1_tarski(esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( k1_relat_1(esk10_0) != k1_tarski(esk8_0)
    | k2_relat_1(esk10_0) != k1_tarski(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_16,plain,(
    ! [X34,X35,X36,X38,X39,X40,X41,X43] :
      ( ( ~ r2_hidden(X36,X35)
        | r2_hidden(k4_tarski(esk5_3(X34,X35,X36),X36),X34)
        | X35 != k2_relat_1(X34) )
      & ( ~ r2_hidden(k4_tarski(X39,X38),X34)
        | r2_hidden(X38,X35)
        | X35 != k2_relat_1(X34) )
      & ( ~ r2_hidden(esk6_2(X40,X41),X41)
        | ~ r2_hidden(k4_tarski(X43,esk6_2(X40,X41)),X40)
        | X41 = k2_relat_1(X40) )
      & ( r2_hidden(esk6_2(X40,X41),X41)
        | r2_hidden(k4_tarski(esk7_2(X40,X41),esk6_2(X40,X41)),X40)
        | X41 = k2_relat_1(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X2) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( esk10_0 = k1_tarski(k4_tarski(esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( k1_relat_1(esk10_0) != k2_tarski(esk8_0,esk8_0)
    | k2_relat_1(esk10_0) != k2_tarski(esk9_0,esk9_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_13]),c_0_13])).

cnf(c_0_20,plain,
    ( X2 = k2_tarski(X1,X1)
    | esk1_2(X1,X2) = X1
    | r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_13])).

cnf(c_0_21,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k2_tarski(X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_17])])).

cnf(c_0_23,negated_conjecture,
    ( esk10_0 = k2_tarski(k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_13])).

fof(c_0_24,plain,(
    ! [X23,X24,X25,X27,X28,X29,X30,X32] :
      ( ( ~ r2_hidden(X25,X24)
        | r2_hidden(k4_tarski(X25,esk2_3(X23,X24,X25)),X23)
        | X24 != k1_relat_1(X23) )
      & ( ~ r2_hidden(k4_tarski(X27,X28),X23)
        | r2_hidden(X27,X24)
        | X24 != k1_relat_1(X23) )
      & ( ~ r2_hidden(esk3_2(X29,X30),X30)
        | ~ r2_hidden(k4_tarski(esk3_2(X29,X30),X32),X29)
        | X30 = k1_relat_1(X29) )
      & ( r2_hidden(esk3_2(X29,X30),X30)
        | r2_hidden(k4_tarski(esk3_2(X29,X30),esk4_2(X29,X30)),X29)
        | X30 = k1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_25,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( esk1_2(esk8_0,k1_relat_1(esk10_0)) = esk8_0
    | r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))
    | k2_tarski(esk9_0,esk9_0) != k2_relat_1(esk10_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk9_0),esk10_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( X2 = k2_tarski(X1,X1)
    | esk1_2(X1,X2) != X1
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_13])).

cnf(c_0_31,negated_conjecture,
    ( esk1_2(esk9_0,k2_relat_1(esk10_0)) = esk9_0
    | esk1_2(esk8_0,k1_relat_1(esk10_0)) = esk8_0
    | r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))
    | r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_20])])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk9_0,k2_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( esk1_2(esk8_0,k1_relat_1(esk10_0)) = esk8_0
    | r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))
    | r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])]),c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk8_0,k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_28])).

fof(c_0_36,plain,(
    ! [X17,X18,X19,X20] :
      ( ( r2_hidden(X17,X19)
        | ~ r2_hidden(k4_tarski(X17,X18),k2_zfmisc_1(X19,k1_tarski(X20))) )
      & ( X18 = X20
        | ~ r2_hidden(k4_tarski(X17,X18),k2_zfmisc_1(X19,k1_tarski(X20))) )
      & ( ~ r2_hidden(X17,X19)
        | X18 != X20
        | r2_hidden(k4_tarski(X17,X18),k2_zfmisc_1(X19,k1_tarski(X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t129_zfmisc_1])])])).

fof(c_0_37,plain,(
    ! [X21,X22] : k2_zfmisc_1(k1_tarski(X21),k1_tarski(X22)) = k1_tarski(k4_tarski(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t35_zfmisc_1])).

cnf(c_0_38,negated_conjecture,
    ( k2_tarski(esk8_0,esk8_0) = k1_relat_1(esk10_0)
    | r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))
    | r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_34]),c_0_35])])).

cnf(c_0_39,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_40,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))
    | r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))
    | k2_tarski(esk9_0,esk9_0) != k2_relat_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_38])).

cnf(c_0_42,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k2_tarski(X2,X2))) ),
    inference(rw,[status(thm)],[c_0_39,c_0_13])).

cnf(c_0_43,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X2,X2)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_13]),c_0_13]),c_0_13])).

cnf(c_0_44,plain,
    ( r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_45,negated_conjecture,
    ( esk1_2(esk9_0,k2_relat_1(esk10_0)) = esk9_0
    | r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))
    | r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_20])])).

fof(c_0_46,plain,(
    ! [X13,X14,X15,X16] :
      ( ( X13 = X15
        | ~ r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(k1_tarski(X15),X16)) )
      & ( r2_hidden(X14,X16)
        | ~ r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(k1_tarski(X15),X16)) )
      & ( X13 != X15
        | ~ r2_hidden(X14,X16)
        | r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(k1_tarski(X15),X16)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t128_zfmisc_1])])])).

cnf(c_0_47,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k2_tarski(k4_tarski(X4,X2),k4_tarski(X4,X2))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))
    | r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_45]),c_0_32])]),c_0_41])).

cnf(c_0_50,plain,
    ( X1 = k2_tarski(X2,X2)
    | r2_hidden(esk1_2(X2,X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_20])).

cnf(c_0_51,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( X1 = esk9_0
    | ~ r2_hidden(k4_tarski(X2,X1),esk10_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_23])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_3(esk10_0,k2_relat_1(esk10_0),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk10_0)
    | r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( k2_tarski(esk8_0,esk8_0) = k1_relat_1(esk10_0)
    | r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_35])).

cnf(c_0_55,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k2_tarski(X2,X2),X4)) ),
    inference(rw,[status(thm)],[c_0_51,c_0_13])).

cnf(c_0_56,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_57,negated_conjecture,
    ( esk1_2(esk9_0,k2_relat_1(esk10_0)) = esk9_0
    | r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))
    | k2_tarski(esk9_0,esk9_0) != k2_relat_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_54])).

cnf(c_0_59,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_tarski(k4_tarski(X2,X4),k4_tarski(X2,X4))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_43])).

cnf(c_0_60,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_57]),c_0_32])]),c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( X1 = esk8_0
    | ~ r2_hidden(k4_tarski(X1,X2),esk10_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_23])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk8_0,k1_relat_1(esk10_0)),esk2_3(esk10_0,k1_relat_1(esk10_0),esk1_2(esk8_0,k1_relat_1(esk10_0)))),esk10_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( esk1_2(esk8_0,k1_relat_1(esk10_0)) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_65,negated_conjecture,
    ( k2_tarski(esk8_0,esk8_0) = k1_relat_1(esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_64]),c_0_35])])).

cnf(c_0_66,negated_conjecture,
    ( k2_tarski(esk9_0,esk9_0) = k2_relat_1(esk10_0)
    | r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_32])).

cnf(c_0_67,negated_conjecture,
    ( k2_tarski(esk9_0,esk9_0) != k2_relat_1(esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_65])])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0)) ),
    inference(sr,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_3(esk10_0,k2_relat_1(esk10_0),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk10_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_68])).

cnf(c_0_70,negated_conjecture,
    ( esk1_2(esk9_0,k2_relat_1(esk10_0)) = esk9_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_69])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_70]),c_0_32])]),c_0_67]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:43:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.56/0.77  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 0.56/0.77  # and selection function SelectCQIArEqFirst.
% 0.56/0.77  #
% 0.56/0.77  # Preprocessing time       : 0.029 s
% 0.56/0.77  # Presaturation interreduction done
% 0.56/0.77  
% 0.56/0.77  # Proof found!
% 0.56/0.77  # SZS status Theorem
% 0.56/0.77  # SZS output start CNFRefutation
% 0.56/0.77  fof(t23_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(X3=k1_tarski(k4_tarski(X1,X2))=>(k1_relat_1(X3)=k1_tarski(X1)&k2_relat_1(X3)=k1_tarski(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_relat_1)).
% 0.56/0.77  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.56/0.77  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.56/0.77  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.56/0.77  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.56/0.77  fof(t129_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X4)))<=>(r2_hidden(X1,X3)&X2=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 0.56/0.77  fof(t35_zfmisc_1, axiom, ![X1, X2]:k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 0.56/0.77  fof(t128_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))<=>(X1=X3&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 0.56/0.77  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(X3=k1_tarski(k4_tarski(X1,X2))=>(k1_relat_1(X3)=k1_tarski(X1)&k2_relat_1(X3)=k1_tarski(X2))))), inference(assume_negation,[status(cth)],[t23_relat_1])).
% 0.56/0.77  fof(c_0_9, plain, ![X5, X6, X7, X8, X9, X10]:(((~r2_hidden(X7,X6)|X7=X5|X6!=k1_tarski(X5))&(X8!=X5|r2_hidden(X8,X6)|X6!=k1_tarski(X5)))&((~r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)!=X9|X10=k1_tarski(X9))&(r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)=X9|X10=k1_tarski(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.56/0.77  fof(c_0_10, plain, ![X12]:k2_tarski(X12,X12)=k1_tarski(X12), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.56/0.77  fof(c_0_11, negated_conjecture, (v1_relat_1(esk10_0)&(esk10_0=k1_tarski(k4_tarski(esk8_0,esk9_0))&(k1_relat_1(esk10_0)!=k1_tarski(esk8_0)|k2_relat_1(esk10_0)!=k1_tarski(esk9_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.56/0.77  cnf(c_0_12, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.56/0.77  cnf(c_0_13, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.56/0.77  cnf(c_0_14, negated_conjecture, (k1_relat_1(esk10_0)!=k1_tarski(esk8_0)|k2_relat_1(esk10_0)!=k1_tarski(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.56/0.77  cnf(c_0_15, plain, (r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.56/0.77  fof(c_0_16, plain, ![X34, X35, X36, X38, X39, X40, X41, X43]:(((~r2_hidden(X36,X35)|r2_hidden(k4_tarski(esk5_3(X34,X35,X36),X36),X34)|X35!=k2_relat_1(X34))&(~r2_hidden(k4_tarski(X39,X38),X34)|r2_hidden(X38,X35)|X35!=k2_relat_1(X34)))&((~r2_hidden(esk6_2(X40,X41),X41)|~r2_hidden(k4_tarski(X43,esk6_2(X40,X41)),X40)|X41=k2_relat_1(X40))&(r2_hidden(esk6_2(X40,X41),X41)|r2_hidden(k4_tarski(esk7_2(X40,X41),esk6_2(X40,X41)),X40)|X41=k2_relat_1(X40)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.56/0.77  cnf(c_0_17, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X2)), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.56/0.77  cnf(c_0_18, negated_conjecture, (esk10_0=k1_tarski(k4_tarski(esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.56/0.77  cnf(c_0_19, negated_conjecture, (k1_relat_1(esk10_0)!=k2_tarski(esk8_0,esk8_0)|k2_relat_1(esk10_0)!=k2_tarski(esk9_0,esk9_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_13]), c_0_13])).
% 0.56/0.77  cnf(c_0_20, plain, (X2=k2_tarski(X1,X1)|esk1_2(X1,X2)=X1|r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[c_0_15, c_0_13])).
% 0.56/0.77  cnf(c_0_21, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.56/0.77  cnf(c_0_22, plain, (r2_hidden(X1,k2_tarski(X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_17])])).
% 0.56/0.77  cnf(c_0_23, negated_conjecture, (esk10_0=k2_tarski(k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0))), inference(rw,[status(thm)],[c_0_18, c_0_13])).
% 0.56/0.77  fof(c_0_24, plain, ![X23, X24, X25, X27, X28, X29, X30, X32]:(((~r2_hidden(X25,X24)|r2_hidden(k4_tarski(X25,esk2_3(X23,X24,X25)),X23)|X24!=k1_relat_1(X23))&(~r2_hidden(k4_tarski(X27,X28),X23)|r2_hidden(X27,X24)|X24!=k1_relat_1(X23)))&((~r2_hidden(esk3_2(X29,X30),X30)|~r2_hidden(k4_tarski(esk3_2(X29,X30),X32),X29)|X30=k1_relat_1(X29))&(r2_hidden(esk3_2(X29,X30),X30)|r2_hidden(k4_tarski(esk3_2(X29,X30),esk4_2(X29,X30)),X29)|X30=k1_relat_1(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.56/0.77  cnf(c_0_25, plain, (X2=k1_tarski(X1)|~r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.56/0.77  cnf(c_0_26, negated_conjecture, (esk1_2(esk8_0,k1_relat_1(esk10_0))=esk8_0|r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))|k2_tarski(esk9_0,esk9_0)!=k2_relat_1(esk10_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20])])).
% 0.56/0.77  cnf(c_0_27, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_21])).
% 0.56/0.77  cnf(c_0_28, negated_conjecture, (r2_hidden(k4_tarski(esk8_0,esk9_0),esk10_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.56/0.77  cnf(c_0_29, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.56/0.77  cnf(c_0_30, plain, (X2=k2_tarski(X1,X1)|esk1_2(X1,X2)!=X1|~r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[c_0_25, c_0_13])).
% 0.56/0.77  cnf(c_0_31, negated_conjecture, (esk1_2(esk9_0,k2_relat_1(esk10_0))=esk9_0|esk1_2(esk8_0,k1_relat_1(esk10_0))=esk8_0|r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))|r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_20])])).
% 0.56/0.77  cnf(c_0_32, negated_conjecture, (r2_hidden(esk9_0,k2_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.56/0.77  cnf(c_0_33, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_29])).
% 0.56/0.77  cnf(c_0_34, negated_conjecture, (esk1_2(esk8_0,k1_relat_1(esk10_0))=esk8_0|r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))|r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])]), c_0_26])).
% 0.56/0.77  cnf(c_0_35, negated_conjecture, (r2_hidden(esk8_0,k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_33, c_0_28])).
% 0.56/0.77  fof(c_0_36, plain, ![X17, X18, X19, X20]:(((r2_hidden(X17,X19)|~r2_hidden(k4_tarski(X17,X18),k2_zfmisc_1(X19,k1_tarski(X20))))&(X18=X20|~r2_hidden(k4_tarski(X17,X18),k2_zfmisc_1(X19,k1_tarski(X20)))))&(~r2_hidden(X17,X19)|X18!=X20|r2_hidden(k4_tarski(X17,X18),k2_zfmisc_1(X19,k1_tarski(X20))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t129_zfmisc_1])])])).
% 0.56/0.77  fof(c_0_37, plain, ![X21, X22]:k2_zfmisc_1(k1_tarski(X21),k1_tarski(X22))=k1_tarski(k4_tarski(X21,X22)), inference(variable_rename,[status(thm)],[t35_zfmisc_1])).
% 0.56/0.77  cnf(c_0_38, negated_conjecture, (k2_tarski(esk8_0,esk8_0)=k1_relat_1(esk10_0)|r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))|r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_34]), c_0_35])])).
% 0.56/0.77  cnf(c_0_39, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.56/0.77  cnf(c_0_40, plain, (k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.56/0.77  cnf(c_0_41, negated_conjecture, (r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))|r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))|k2_tarski(esk9_0,esk9_0)!=k2_relat_1(esk10_0)), inference(spm,[status(thm)],[c_0_19, c_0_38])).
% 0.56/0.77  cnf(c_0_42, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k2_tarski(X2,X2)))), inference(rw,[status(thm)],[c_0_39, c_0_13])).
% 0.56/0.77  cnf(c_0_43, plain, (k2_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X2,X2))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_13]), c_0_13]), c_0_13])).
% 0.56/0.77  cnf(c_0_44, plain, (r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.56/0.77  cnf(c_0_45, negated_conjecture, (esk1_2(esk9_0,k2_relat_1(esk10_0))=esk9_0|r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))|r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_20])])).
% 0.56/0.77  fof(c_0_46, plain, ![X13, X14, X15, X16]:(((X13=X15|~r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(k1_tarski(X15),X16)))&(r2_hidden(X14,X16)|~r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(k1_tarski(X15),X16))))&(X13!=X15|~r2_hidden(X14,X16)|r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(k1_tarski(X15),X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t128_zfmisc_1])])])).
% 0.56/0.77  cnf(c_0_47, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_tarski(k4_tarski(X4,X2),k4_tarski(X4,X2)))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.56/0.77  cnf(c_0_48, plain, (r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_44])).
% 0.56/0.77  cnf(c_0_49, negated_conjecture, (r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))|r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_45]), c_0_32])]), c_0_41])).
% 0.56/0.77  cnf(c_0_50, plain, (X1=k2_tarski(X2,X2)|r2_hidden(esk1_2(X2,X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_30, c_0_20])).
% 0.56/0.77  cnf(c_0_51, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),X4))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.56/0.77  cnf(c_0_52, negated_conjecture, (X1=esk9_0|~r2_hidden(k4_tarski(X2,X1),esk10_0)), inference(spm,[status(thm)],[c_0_47, c_0_23])).
% 0.56/0.77  cnf(c_0_53, negated_conjecture, (r2_hidden(k4_tarski(esk5_3(esk10_0,k2_relat_1(esk10_0),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk10_0)|r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.56/0.77  cnf(c_0_54, negated_conjecture, (k2_tarski(esk8_0,esk8_0)=k1_relat_1(esk10_0)|r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_50, c_0_35])).
% 0.56/0.77  cnf(c_0_55, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k2_tarski(X2,X2),X4))), inference(rw,[status(thm)],[c_0_51, c_0_13])).
% 0.56/0.77  cnf(c_0_56, plain, (r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.56/0.77  cnf(c_0_57, negated_conjecture, (esk1_2(esk9_0,k2_relat_1(esk10_0))=esk9_0|r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.56/0.77  cnf(c_0_58, negated_conjecture, (r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))|k2_tarski(esk9_0,esk9_0)!=k2_relat_1(esk10_0)), inference(spm,[status(thm)],[c_0_19, c_0_54])).
% 0.56/0.77  cnf(c_0_59, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_tarski(k4_tarski(X2,X4),k4_tarski(X2,X4)))), inference(spm,[status(thm)],[c_0_55, c_0_43])).
% 0.56/0.77  cnf(c_0_60, plain, (r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_56])).
% 0.56/0.77  cnf(c_0_61, negated_conjecture, (r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_57]), c_0_32])]), c_0_58])).
% 0.56/0.77  cnf(c_0_62, negated_conjecture, (X1=esk8_0|~r2_hidden(k4_tarski(X1,X2),esk10_0)), inference(spm,[status(thm)],[c_0_59, c_0_23])).
% 0.56/0.77  cnf(c_0_63, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk8_0,k1_relat_1(esk10_0)),esk2_3(esk10_0,k1_relat_1(esk10_0),esk1_2(esk8_0,k1_relat_1(esk10_0)))),esk10_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.56/0.77  cnf(c_0_64, negated_conjecture, (esk1_2(esk8_0,k1_relat_1(esk10_0))=esk8_0), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.56/0.77  cnf(c_0_65, negated_conjecture, (k2_tarski(esk8_0,esk8_0)=k1_relat_1(esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_64]), c_0_35])])).
% 0.56/0.77  cnf(c_0_66, negated_conjecture, (k2_tarski(esk9_0,esk9_0)=k2_relat_1(esk10_0)|r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_50, c_0_32])).
% 0.56/0.77  cnf(c_0_67, negated_conjecture, (k2_tarski(esk9_0,esk9_0)!=k2_relat_1(esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_65])])).
% 0.56/0.77  cnf(c_0_68, negated_conjecture, (r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))), inference(sr,[status(thm)],[c_0_66, c_0_67])).
% 0.56/0.77  cnf(c_0_69, negated_conjecture, (r2_hidden(k4_tarski(esk5_3(esk10_0,k2_relat_1(esk10_0),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk10_0)), inference(spm,[status(thm)],[c_0_48, c_0_68])).
% 0.56/0.77  cnf(c_0_70, negated_conjecture, (esk1_2(esk9_0,k2_relat_1(esk10_0))=esk9_0), inference(spm,[status(thm)],[c_0_52, c_0_69])).
% 0.56/0.77  cnf(c_0_71, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_70]), c_0_32])]), c_0_67]), ['proof']).
% 0.56/0.77  # SZS output end CNFRefutation
% 0.56/0.77  # Proof object total steps             : 72
% 0.56/0.77  # Proof object clause steps            : 55
% 0.56/0.77  # Proof object formula steps           : 17
% 0.56/0.77  # Proof object conjectures             : 33
% 0.56/0.77  # Proof object clause conjectures      : 30
% 0.56/0.77  # Proof object formula conjectures     : 3
% 0.56/0.77  # Proof object initial clauses used    : 13
% 0.56/0.77  # Proof object initial formulas used   : 8
% 0.56/0.77  # Proof object generating inferences   : 27
% 0.56/0.77  # Proof object simplifying inferences  : 39
% 0.56/0.77  # Training examples: 0 positive, 0 negative
% 0.56/0.77  # Parsed axioms                        : 8
% 0.56/0.77  # Removed by relevancy pruning/SinE    : 0
% 0.56/0.77  # Initial clauses                      : 23
% 0.56/0.77  # Removed in clause preprocessing      : 1
% 0.56/0.77  # Initial clauses in saturation        : 22
% 0.56/0.77  # Processed clauses                    : 1058
% 0.56/0.77  # ...of these trivial                  : 12
% 0.56/0.77  # ...subsumed                          : 343
% 0.56/0.77  # ...remaining for further processing  : 703
% 0.56/0.77  # Other redundant clauses eliminated   : 85
% 0.56/0.77  # Clauses deleted for lack of memory   : 0
% 0.56/0.77  # Backward-subsumed                    : 37
% 0.56/0.77  # Backward-rewritten                   : 188
% 0.56/0.77  # Generated clauses                    : 31842
% 0.56/0.77  # ...of the previous two non-trivial   : 29820
% 0.56/0.77  # Contextual simplify-reflections      : 5
% 0.56/0.77  # Paramodulations                      : 31745
% 0.56/0.77  # Factorizations                       : 11
% 0.56/0.77  # Equation resolutions                 : 86
% 0.56/0.77  # Propositional unsat checks           : 0
% 0.56/0.77  #    Propositional check models        : 0
% 0.56/0.77  #    Propositional check unsatisfiable : 0
% 0.56/0.77  #    Propositional clauses             : 0
% 0.56/0.77  #    Propositional clauses after purity: 0
% 0.56/0.77  #    Propositional unsat core size     : 0
% 0.56/0.77  #    Propositional preprocessing time  : 0.000
% 0.56/0.77  #    Propositional encoding time       : 0.000
% 0.56/0.77  #    Propositional solver time         : 0.000
% 0.56/0.77  #    Success case prop preproc time    : 0.000
% 0.56/0.77  #    Success case prop encoding time   : 0.000
% 0.56/0.77  #    Success case prop solver time     : 0.000
% 0.56/0.77  # Current number of processed clauses  : 447
% 0.56/0.77  #    Positive orientable unit clauses  : 238
% 0.56/0.77  #    Positive unorientable unit clauses: 0
% 0.56/0.77  #    Negative unit clauses             : 1
% 0.56/0.77  #    Non-unit-clauses                  : 208
% 0.56/0.77  # Current number of unprocessed clauses: 28704
% 0.56/0.77  # ...number of literals in the above   : 133084
% 0.56/0.77  # Current number of archived formulas  : 0
% 0.56/0.77  # Current number of archived clauses   : 249
% 0.56/0.77  # Clause-clause subsumption calls (NU) : 18673
% 0.56/0.77  # Rec. Clause-clause subsumption calls : 10266
% 0.56/0.77  # Non-unit clause-clause subsumptions  : 374
% 0.56/0.77  # Unit Clause-clause subsumption calls : 5631
% 0.56/0.77  # Rewrite failures with RHS unbound    : 0
% 0.56/0.77  # BW rewrite match attempts            : 1383
% 0.56/0.77  # BW rewrite match successes           : 19
% 0.56/0.77  # Condensation attempts                : 0
% 0.56/0.77  # Condensation successes               : 0
% 0.56/0.77  # Termbank termtop insertions          : 695578
% 0.56/0.77  
% 0.56/0.77  # -------------------------------------------------
% 0.56/0.77  # User time                : 0.401 s
% 0.56/0.77  # System time              : 0.024 s
% 0.56/0.77  # Total time               : 0.425 s
% 0.56/0.77  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
