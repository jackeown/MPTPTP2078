%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:57 EST 2020

% Result     : Theorem 0.45s
% Output     : CNFRefutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 533 expanded)
%              Number of clauses        :   45 ( 228 expanded)
%              Number of leaves         :    7 ( 147 expanded)
%              Depth                    :   16
%              Number of atoms          :  211 (2020 expanded)
%              Number of equality atoms :  106 ( 953 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t15_funct_1,conjecture,(
    ! [X1] :
      ( X1 != k1_xboole_0
     => ! [X2] :
        ? [X3] :
          ( v1_relat_1(X3)
          & v1_funct_1(X3)
          & k1_relat_1(X3) = X1
          & k2_relat_1(X3) = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(l44_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(s3_funct_1__e2_24__funct_1,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( v1_relat_1(X3)
      & v1_funct_1(X3)
      & k1_relat_1(X3) = X1
      & ! [X4] :
          ( r2_hidden(X4,X1)
         => k1_funct_1(X3,X4) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( X1 != k1_xboole_0
       => ! [X2] :
          ? [X3] :
            ( v1_relat_1(X3)
            & v1_funct_1(X3)
            & k1_relat_1(X3) = X1
            & k2_relat_1(X3) = k1_tarski(X2) ) ) ),
    inference(assume_negation,[status(cth)],[t15_funct_1])).

fof(c_0_8,plain,(
    ! [X18,X19,X20,X22,X23,X24,X26] :
      ( ( r2_hidden(esk3_3(X18,X19,X20),k1_relat_1(X18))
        | ~ r2_hidden(X20,X19)
        | X19 != k2_relat_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( X20 = k1_funct_1(X18,esk3_3(X18,X19,X20))
        | ~ r2_hidden(X20,X19)
        | X19 != k2_relat_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( ~ r2_hidden(X23,k1_relat_1(X18))
        | X22 != k1_funct_1(X18,X23)
        | r2_hidden(X22,X19)
        | X19 != k2_relat_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( ~ r2_hidden(esk4_2(X18,X24),X24)
        | ~ r2_hidden(X26,k1_relat_1(X18))
        | esk4_2(X18,X24) != k1_funct_1(X18,X26)
        | X24 = k2_relat_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( r2_hidden(esk5_2(X18,X24),k1_relat_1(X18))
        | r2_hidden(esk4_2(X18,X24),X24)
        | X24 = k2_relat_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( esk4_2(X18,X24) = k1_funct_1(X18,esk5_2(X18,X24))
        | r2_hidden(esk4_2(X18,X24),X24)
        | X24 = k2_relat_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_9,negated_conjecture,(
    ! [X34] :
      ( esk7_0 != k1_xboole_0
      & ( ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34)
        | k1_relat_1(X34) != esk7_0
        | k2_relat_1(X34) != k1_tarski(esk8_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

fof(c_0_10,plain,(
    ! [X12] : k2_tarski(X12,X12) = k1_tarski(X12) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_11,plain,(
    ! [X13,X14] : k1_enumset1(X13,X13,X14) = k2_tarski(X13,X14) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X15,X16] :
      ( ( r2_hidden(esk2_2(X15,X16),X15)
        | X15 = k1_tarski(X16)
        | X15 = k1_xboole_0 )
      & ( esk2_2(X15,X16) != X16
        | X15 = k1_tarski(X16)
        | X15 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_14,plain,(
    ! [X28,X29,X31] :
      ( v1_relat_1(esk6_2(X28,X29))
      & v1_funct_1(esk6_2(X28,X29))
      & k1_relat_1(esk6_2(X28,X29)) = X28
      & ( ~ r2_hidden(X31,X28)
        | k1_funct_1(esk6_2(X28,X29),X31) = X29 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).

cnf(c_0_15,negated_conjecture,
    ( ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_relat_1(X1) != esk7_0
    | k2_relat_1(X1) != k1_tarski(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( X1 = k1_funct_1(X2,esk3_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,plain,
    ( r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k1_relat_1(esk6_2(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( v1_funct_1(esk6_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( v1_relat_1(esk6_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( k1_relat_1(X1) != esk7_0
    | k2_relat_1(X1) != k1_enumset1(esk8_0,esk8_0,esk8_0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_25,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_enumset1(X2,X2,X2)
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_16]),c_0_17])).

cnf(c_0_26,plain,
    ( k1_funct_1(esk6_2(X2,X3),X1) = X3
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,plain,
    ( k1_funct_1(X1,esk3_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( r2_hidden(esk3_3(esk6_2(X1,X2),k2_relat_1(esk6_2(X1,X2)),X3),X1)
    | ~ r2_hidden(X3,k2_relat_1(esk6_2(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_29,negated_conjecture,
    ( k2_relat_1(X1) = k1_xboole_0
    | r2_hidden(esk2_2(k2_relat_1(X1),esk8_0),k2_relat_1(X1))
    | k1_relat_1(X1) != esk7_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25])])).

cnf(c_0_30,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | esk2_2(X1,X2) != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_31,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_relat_1(esk6_2(X3,X2))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_22]),c_0_23])]),c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( k2_relat_1(esk6_2(esk7_0,X1)) = k1_xboole_0
    | r2_hidden(esk2_2(k2_relat_1(esk6_2(esk7_0,X1)),esk8_0),k2_relat_1(esk6_2(esk7_0,X1))) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_21]),c_0_22]),c_0_23])])])).

fof(c_0_33,plain,(
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

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_enumset1(X2,X2,X2)
    | esk2_2(X1,X2) != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_16]),c_0_17])).

cnf(c_0_35,negated_conjecture,
    ( esk2_2(k2_relat_1(esk6_2(esk7_0,X1)),esk8_0) = X1
    | k2_relat_1(esk6_2(esk7_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( k1_enumset1(esk8_0,esk8_0,esk8_0) = k2_relat_1(esk6_2(esk7_0,esk8_0))
    | k2_relat_1(esk6_2(esk7_0,esk8_0)) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35])])).

cnf(c_0_38,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_16]),c_0_17])).

cnf(c_0_40,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( k2_relat_1(esk6_2(esk7_0,esk8_0)) = k1_xboole_0
    | k2_relat_1(X1) != k2_relat_1(esk6_2(esk7_0,esk8_0))
    | k1_relat_1(X1) != esk7_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_37])).

cnf(c_0_42,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_38])])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_39])])).

cnf(c_0_44,plain,
    ( esk1_2(X1,X2) = X1
    | X2 = k1_enumset1(X1,X1,X1)
    | r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_16]),c_0_17])).

cnf(c_0_45,negated_conjecture,
    ( k2_relat_1(esk6_2(esk7_0,esk8_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_41]),c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,k2_relat_1(esk6_2(X2,X1)))
    | ~ r2_hidden(X3,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_26]),c_0_22]),c_0_23]),c_0_21])])).

cnf(c_0_47,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_2(X1,X2),X1)
    | r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_25])).

cnf(c_0_48,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_49,negated_conjecture,
    ( esk1_2(esk8_0,k2_relat_1(X1)) = esk8_0
    | r2_hidden(esk1_2(esk8_0,k2_relat_1(X1)),k2_relat_1(X1))
    | k1_relat_1(X1) != esk7_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_44])])).

cnf(c_0_50,negated_conjecture,
    ( X1 = esk8_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_45])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k2_relat_1(esk6_2(X1,X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_53,plain,
    ( X2 = k1_enumset1(X1,X1,X1)
    | esk1_2(X1,X2) != X1
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_16]),c_0_17])).

cnf(c_0_54,negated_conjecture,
    ( esk1_2(esk8_0,k1_xboole_0) = esk8_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_45]),c_0_21]),c_0_22]),c_0_23])]),c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk8_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_45]),c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( k1_enumset1(esk8_0,esk8_0,esk8_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])])).

cnf(c_0_57,negated_conjecture,
    ( k2_relat_1(X1) != k1_xboole_0
    | k1_relat_1(X1) != esk7_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_24,c_0_56])).

cnf(c_0_58,negated_conjecture,
    ( k2_relat_1(esk6_2(esk7_0,X1)) != k1_xboole_0 ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_21]),c_0_22]),c_0_23])])])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_45,c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:57:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.45/0.61  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.45/0.61  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.45/0.61  #
% 0.45/0.61  # Preprocessing time       : 0.027 s
% 0.45/0.61  # Presaturation interreduction done
% 0.45/0.61  
% 0.45/0.61  # Proof found!
% 0.45/0.61  # SZS status Theorem
% 0.45/0.61  # SZS output start CNFRefutation
% 0.45/0.61  fof(t15_funct_1, conjecture, ![X1]:(X1!=k1_xboole_0=>![X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&k2_relat_1(X3)=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 0.45/0.61  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 0.45/0.61  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.45/0.61  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.45/0.61  fof(l44_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 0.45/0.61  fof(s3_funct_1__e2_24__funct_1, axiom, ![X1, X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&![X4]:(r2_hidden(X4,X1)=>k1_funct_1(X3,X4)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 0.45/0.61  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.45/0.61  fof(c_0_7, negated_conjecture, ~(![X1]:(X1!=k1_xboole_0=>![X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&k2_relat_1(X3)=k1_tarski(X2)))), inference(assume_negation,[status(cth)],[t15_funct_1])).
% 0.45/0.61  fof(c_0_8, plain, ![X18, X19, X20, X22, X23, X24, X26]:((((r2_hidden(esk3_3(X18,X19,X20),k1_relat_1(X18))|~r2_hidden(X20,X19)|X19!=k2_relat_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(X20=k1_funct_1(X18,esk3_3(X18,X19,X20))|~r2_hidden(X20,X19)|X19!=k2_relat_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18))))&(~r2_hidden(X23,k1_relat_1(X18))|X22!=k1_funct_1(X18,X23)|r2_hidden(X22,X19)|X19!=k2_relat_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18))))&((~r2_hidden(esk4_2(X18,X24),X24)|(~r2_hidden(X26,k1_relat_1(X18))|esk4_2(X18,X24)!=k1_funct_1(X18,X26))|X24=k2_relat_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))&((r2_hidden(esk5_2(X18,X24),k1_relat_1(X18))|r2_hidden(esk4_2(X18,X24),X24)|X24=k2_relat_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(esk4_2(X18,X24)=k1_funct_1(X18,esk5_2(X18,X24))|r2_hidden(esk4_2(X18,X24),X24)|X24=k2_relat_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.45/0.61  fof(c_0_9, negated_conjecture, ![X34]:(esk7_0!=k1_xboole_0&(~v1_relat_1(X34)|~v1_funct_1(X34)|k1_relat_1(X34)!=esk7_0|k2_relat_1(X34)!=k1_tarski(esk8_0))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).
% 0.45/0.61  fof(c_0_10, plain, ![X12]:k2_tarski(X12,X12)=k1_tarski(X12), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.45/0.61  fof(c_0_11, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.45/0.61  fof(c_0_12, plain, ![X15, X16]:((r2_hidden(esk2_2(X15,X16),X15)|(X15=k1_tarski(X16)|X15=k1_xboole_0))&(esk2_2(X15,X16)!=X16|(X15=k1_tarski(X16)|X15=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).
% 0.45/0.61  cnf(c_0_13, plain, (r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.45/0.61  fof(c_0_14, plain, ![X28, X29, X31]:(((v1_relat_1(esk6_2(X28,X29))&v1_funct_1(esk6_2(X28,X29)))&k1_relat_1(esk6_2(X28,X29))=X28)&(~r2_hidden(X31,X28)|k1_funct_1(esk6_2(X28,X29),X31)=X29)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).
% 0.45/0.61  cnf(c_0_15, negated_conjecture, (~v1_relat_1(X1)|~v1_funct_1(X1)|k1_relat_1(X1)!=esk7_0|k2_relat_1(X1)!=k1_tarski(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.45/0.61  cnf(c_0_16, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.45/0.61  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.45/0.61  cnf(c_0_18, plain, (r2_hidden(esk2_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.45/0.61  cnf(c_0_19, plain, (X1=k1_funct_1(X2,esk3_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.45/0.61  cnf(c_0_20, plain, (r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_13])).
% 0.45/0.61  cnf(c_0_21, plain, (k1_relat_1(esk6_2(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.45/0.61  cnf(c_0_22, plain, (v1_funct_1(esk6_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.45/0.61  cnf(c_0_23, plain, (v1_relat_1(esk6_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.45/0.61  cnf(c_0_24, negated_conjecture, (k1_relat_1(X1)!=esk7_0|k2_relat_1(X1)!=k1_enumset1(esk8_0,esk8_0,esk8_0)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 0.45/0.61  cnf(c_0_25, plain, (X1=k1_xboole_0|X1=k1_enumset1(X2,X2,X2)|r2_hidden(esk2_2(X1,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_16]), c_0_17])).
% 0.45/0.61  cnf(c_0_26, plain, (k1_funct_1(esk6_2(X2,X3),X1)=X3|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.45/0.61  cnf(c_0_27, plain, (k1_funct_1(X1,esk3_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_19])).
% 0.45/0.61  cnf(c_0_28, plain, (r2_hidden(esk3_3(esk6_2(X1,X2),k2_relat_1(esk6_2(X1,X2)),X3),X1)|~r2_hidden(X3,k2_relat_1(esk6_2(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])])).
% 0.45/0.61  cnf(c_0_29, negated_conjecture, (k2_relat_1(X1)=k1_xboole_0|r2_hidden(esk2_2(k2_relat_1(X1),esk8_0),k2_relat_1(X1))|k1_relat_1(X1)!=esk7_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25])])).
% 0.45/0.61  cnf(c_0_30, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|esk2_2(X1,X2)!=X2), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.45/0.61  cnf(c_0_31, plain, (X1=X2|~r2_hidden(X1,k2_relat_1(esk6_2(X3,X2)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_22]), c_0_23])]), c_0_28])).
% 0.45/0.61  cnf(c_0_32, negated_conjecture, (k2_relat_1(esk6_2(esk7_0,X1))=k1_xboole_0|r2_hidden(esk2_2(k2_relat_1(esk6_2(esk7_0,X1)),esk8_0),k2_relat_1(esk6_2(esk7_0,X1)))), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_21]), c_0_22]), c_0_23])])])).
% 0.45/0.61  fof(c_0_33, plain, ![X5, X6, X7, X8, X9, X10]:(((~r2_hidden(X7,X6)|X7=X5|X6!=k1_tarski(X5))&(X8!=X5|r2_hidden(X8,X6)|X6!=k1_tarski(X5)))&((~r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)!=X9|X10=k1_tarski(X9))&(r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)=X9|X10=k1_tarski(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.45/0.61  cnf(c_0_34, plain, (X1=k1_xboole_0|X1=k1_enumset1(X2,X2,X2)|esk2_2(X1,X2)!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_16]), c_0_17])).
% 0.45/0.61  cnf(c_0_35, negated_conjecture, (esk2_2(k2_relat_1(esk6_2(esk7_0,X1)),esk8_0)=X1|k2_relat_1(esk6_2(esk7_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.45/0.61  cnf(c_0_36, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.45/0.61  cnf(c_0_37, negated_conjecture, (k1_enumset1(esk8_0,esk8_0,esk8_0)=k2_relat_1(esk6_2(esk7_0,esk8_0))|k2_relat_1(esk6_2(esk7_0,esk8_0))=k1_xboole_0), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35])])).
% 0.45/0.61  cnf(c_0_38, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.45/0.61  cnf(c_0_39, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_16]), c_0_17])).
% 0.45/0.61  cnf(c_0_40, plain, (r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.45/0.61  cnf(c_0_41, negated_conjecture, (k2_relat_1(esk6_2(esk7_0,esk8_0))=k1_xboole_0|k2_relat_1(X1)!=k2_relat_1(esk6_2(esk7_0,esk8_0))|k1_relat_1(X1)!=esk7_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_37])).
% 0.45/0.61  cnf(c_0_42, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_38])])).
% 0.45/0.61  cnf(c_0_43, plain, (r2_hidden(X1,k1_enumset1(X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_39])])).
% 0.45/0.61  cnf(c_0_44, plain, (esk1_2(X1,X2)=X1|X2=k1_enumset1(X1,X1,X1)|r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_16]), c_0_17])).
% 0.45/0.61  cnf(c_0_45, negated_conjecture, (k2_relat_1(esk6_2(esk7_0,esk8_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_41]), c_0_21]), c_0_22]), c_0_23])])).
% 0.45/0.61  cnf(c_0_46, plain, (r2_hidden(X1,k2_relat_1(esk6_2(X2,X1)))|~r2_hidden(X3,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_26]), c_0_22]), c_0_23]), c_0_21])])).
% 0.45/0.61  cnf(c_0_47, plain, (X1=k1_xboole_0|r2_hidden(esk2_2(X1,X2),X1)|r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_43, c_0_25])).
% 0.45/0.61  cnf(c_0_48, plain, (X2=k1_tarski(X1)|~r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.45/0.61  cnf(c_0_49, negated_conjecture, (esk1_2(esk8_0,k2_relat_1(X1))=esk8_0|r2_hidden(esk1_2(esk8_0,k2_relat_1(X1)),k2_relat_1(X1))|k1_relat_1(X1)!=esk7_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_44])])).
% 0.45/0.61  cnf(c_0_50, negated_conjecture, (X1=esk8_0|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_31, c_0_45])).
% 0.45/0.61  cnf(c_0_51, plain, (X1=k1_xboole_0|r2_hidden(X2,k2_relat_1(esk6_2(X1,X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_46])).
% 0.45/0.61  cnf(c_0_52, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.45/0.61  cnf(c_0_53, plain, (X2=k1_enumset1(X1,X1,X1)|esk1_2(X1,X2)!=X1|~r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_16]), c_0_17])).
% 0.45/0.61  cnf(c_0_54, negated_conjecture, (esk1_2(esk8_0,k1_xboole_0)=esk8_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_45]), c_0_21]), c_0_22]), c_0_23])]), c_0_50])).
% 0.45/0.61  cnf(c_0_55, negated_conjecture, (r2_hidden(esk8_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_45]), c_0_52])).
% 0.45/0.61  cnf(c_0_56, negated_conjecture, (k1_enumset1(esk8_0,esk8_0,esk8_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])])).
% 0.45/0.61  cnf(c_0_57, negated_conjecture, (k2_relat_1(X1)!=k1_xboole_0|k1_relat_1(X1)!=esk7_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_24, c_0_56])).
% 0.45/0.61  cnf(c_0_58, negated_conjecture, (k2_relat_1(esk6_2(esk7_0,X1))!=k1_xboole_0), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_21]), c_0_22]), c_0_23])])])).
% 0.45/0.61  cnf(c_0_59, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_45, c_0_58]), ['proof']).
% 0.45/0.61  # SZS output end CNFRefutation
% 0.45/0.61  # Proof object total steps             : 60
% 0.45/0.61  # Proof object clause steps            : 45
% 0.45/0.61  # Proof object formula steps           : 15
% 0.45/0.61  # Proof object conjectures             : 20
% 0.45/0.61  # Proof object clause conjectures      : 17
% 0.45/0.61  # Proof object formula conjectures     : 3
% 0.45/0.61  # Proof object initial clauses used    : 16
% 0.45/0.61  # Proof object initial formulas used   : 7
% 0.45/0.61  # Proof object generating inferences   : 17
% 0.45/0.61  # Proof object simplifying inferences  : 55
% 0.45/0.61  # Training examples: 0 positive, 0 negative
% 0.45/0.61  # Parsed axioms                        : 7
% 0.45/0.61  # Removed by relevancy pruning/SinE    : 0
% 0.45/0.61  # Initial clauses                      : 20
% 0.45/0.61  # Removed in clause preprocessing      : 2
% 0.45/0.61  # Initial clauses in saturation        : 18
% 0.45/0.61  # Processed clauses                    : 493
% 0.45/0.61  # ...of these trivial                  : 8
% 0.45/0.61  # ...subsumed                          : 240
% 0.45/0.61  # ...remaining for further processing  : 245
% 0.45/0.61  # Other redundant clauses eliminated   : 692
% 0.45/0.61  # Clauses deleted for lack of memory   : 0
% 0.45/0.61  # Backward-subsumed                    : 28
% 0.45/0.61  # Backward-rewritten                   : 29
% 0.45/0.61  # Generated clauses                    : 15489
% 0.45/0.61  # ...of the previous two non-trivial   : 13616
% 0.45/0.61  # Contextual simplify-reflections      : 12
% 0.45/0.61  # Paramodulations                      : 14724
% 0.45/0.61  # Factorizations                       : 65
% 0.45/0.61  # Equation resolutions                 : 695
% 0.45/0.61  # Propositional unsat checks           : 0
% 0.45/0.61  #    Propositional check models        : 0
% 0.45/0.61  #    Propositional check unsatisfiable : 0
% 0.45/0.61  #    Propositional clauses             : 0
% 0.45/0.61  #    Propositional clauses after purity: 0
% 0.45/0.61  #    Propositional unsat core size     : 0
% 0.45/0.61  #    Propositional preprocessing time  : 0.000
% 0.45/0.61  #    Propositional encoding time       : 0.000
% 0.45/0.61  #    Propositional solver time         : 0.000
% 0.45/0.61  #    Success case prop preproc time    : 0.000
% 0.45/0.61  #    Success case prop encoding time   : 0.000
% 0.45/0.61  #    Success case prop solver time     : 0.000
% 0.45/0.61  # Current number of processed clauses  : 158
% 0.45/0.61  #    Positive orientable unit clauses  : 15
% 0.45/0.61  #    Positive unorientable unit clauses: 0
% 0.45/0.61  #    Negative unit clauses             : 2
% 0.45/0.61  #    Non-unit-clauses                  : 141
% 0.45/0.61  # Current number of unprocessed clauses: 13071
% 0.45/0.61  # ...number of literals in the above   : 83162
% 0.45/0.61  # Current number of archived formulas  : 0
% 0.45/0.61  # Current number of archived clauses   : 84
% 0.45/0.61  # Clause-clause subsumption calls (NU) : 8660
% 0.45/0.61  # Rec. Clause-clause subsumption calls : 2232
% 0.45/0.61  # Non-unit clause-clause subsumptions  : 258
% 0.45/0.61  # Unit Clause-clause subsumption calls : 396
% 0.45/0.61  # Rewrite failures with RHS unbound    : 0
% 0.45/0.61  # BW rewrite match attempts            : 117
% 0.45/0.61  # BW rewrite match successes           : 11
% 0.45/0.61  # Condensation attempts                : 0
% 0.45/0.61  # Condensation successes               : 0
% 0.45/0.61  # Termbank termtop insertions          : 335982
% 0.45/0.61  
% 0.45/0.61  # -------------------------------------------------
% 0.45/0.61  # User time                : 0.261 s
% 0.45/0.61  # System time              : 0.013 s
% 0.45/0.61  # Total time               : 0.275 s
% 0.45/0.61  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
