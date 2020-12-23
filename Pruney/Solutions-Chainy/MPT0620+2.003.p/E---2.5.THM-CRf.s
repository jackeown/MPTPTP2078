%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:57 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   68 (1191 expanded)
%              Number of clauses        :   53 ( 535 expanded)
%              Number of leaves         :    7 ( 325 expanded)
%              Depth                    :   16
%              Number of atoms          :  219 (4587 expanded)
%              Number of equality atoms :   94 (2086 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(s3_funct_1__e2_24__funct_1,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( v1_relat_1(X3)
      & v1_funct_1(X3)
      & k1_relat_1(X3) = X1
      & ! [X4] :
          ( r2_hidden(X4,X1)
         => k1_funct_1(X3,X4) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(t15_funct_1,conjecture,(
    ! [X1] :
      ( X1 != k1_xboole_0
     => ! [X2] :
        ? [X3] :
          ( v1_relat_1(X3)
          & v1_funct_1(X3)
          & k1_relat_1(X3) = X1
          & k2_relat_1(X3) = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(c_0_7,plain,(
    ! [X15] :
      ( ( k1_relat_1(X15) != k1_xboole_0
        | X15 = k1_xboole_0
        | ~ v1_relat_1(X15) )
      & ( k2_relat_1(X15) != k1_xboole_0
        | X15 = k1_xboole_0
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

fof(c_0_8,plain,(
    ! [X26,X27,X29] :
      ( v1_relat_1(esk5_2(X26,X27))
      & v1_funct_1(esk5_2(X26,X27))
      & k1_relat_1(esk5_2(X26,X27)) = X26
      & ( ~ r2_hidden(X29,X26)
        | k1_funct_1(esk5_2(X26,X27),X29) = X27 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).

cnf(c_0_9,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( k1_relat_1(esk5_2(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( v1_relat_1(esk5_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( X1 != k1_xboole_0
       => ! [X2] :
          ? [X3] :
            ( v1_relat_1(X3)
            & v1_funct_1(X3)
            & k1_relat_1(X3) = X1
            & k2_relat_1(X3) = k1_tarski(X2) ) ) ),
    inference(assume_negation,[status(cth)],[t15_funct_1])).

cnf(c_0_13,plain,
    ( k1_funct_1(esk5_2(X2,X3),X1) = X3
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( esk5_2(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])])])).

fof(c_0_15,plain,(
    ! [X16,X17,X18,X20,X21,X22,X24] :
      ( ( r2_hidden(esk2_3(X16,X17,X18),k1_relat_1(X16))
        | ~ r2_hidden(X18,X17)
        | X17 != k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( X18 = k1_funct_1(X16,esk2_3(X16,X17,X18))
        | ~ r2_hidden(X18,X17)
        | X17 != k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( ~ r2_hidden(X21,k1_relat_1(X16))
        | X20 != k1_funct_1(X16,X21)
        | r2_hidden(X20,X17)
        | X17 != k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( ~ r2_hidden(esk3_2(X16,X22),X22)
        | ~ r2_hidden(X24,k1_relat_1(X16))
        | esk3_2(X16,X22) != k1_funct_1(X16,X24)
        | X22 = k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( r2_hidden(esk4_2(X16,X22),k1_relat_1(X16))
        | r2_hidden(esk3_2(X16,X22),X22)
        | X22 = k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( esk3_2(X16,X22) = k1_funct_1(X16,esk4_2(X16,X22))
        | r2_hidden(esk3_2(X16,X22),X22)
        | X22 = k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_16,negated_conjecture,(
    ! [X32] :
      ( esk6_0 != k1_xboole_0
      & ( ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32)
        | k1_relat_1(X32) != esk6_0
        | k2_relat_1(X32) != k1_tarski(esk7_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).

fof(c_0_17,plain,(
    ! [X12] : k2_tarski(X12,X12) = k1_tarski(X12) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_18,plain,(
    ! [X13,X14] : k1_enumset1(X13,X13,X14) = k2_tarski(X13,X14) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_19,plain,
    ( k1_funct_1(k1_xboole_0,X1) = X2
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( v1_funct_1(esk5_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_relat_1(X1) != esk6_0
    | k2_relat_1(X1) != k1_tarski(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( v1_relat_1(k1_funct_1(k1_xboole_0,X1))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_19])).

cnf(c_0_26,plain,
    ( r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_10,c_0_14])).

cnf(c_0_28,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_14])).

cnf(c_0_29,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_14])).

cnf(c_0_30,plain,
    ( v1_funct_1(k1_funct_1(k1_xboole_0,X1))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_19])).

fof(c_0_31,plain,(
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

cnf(c_0_32,negated_conjecture,
    ( k1_relat_1(X1) != esk6_0
    | k2_relat_1(X1) != k1_enumset1(esk7_0,esk7_0,esk7_0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_33,plain,
    ( v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_19])).

cnf(c_0_34,plain,
    ( r2_hidden(esk2_3(k1_xboole_0,k2_relat_1(k1_xboole_0),X1),k1_xboole_0)
    | ~ r2_hidden(X1,k2_relat_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_35,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_19])).

cnf(c_0_36,plain,
    ( X1 = k1_funct_1(X2,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( k1_relat_1(X1) != esk6_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_19]),c_0_19])).

cnf(c_0_39,plain,
    ( v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_34])).

cnf(c_0_41,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_42,plain,
    ( k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( esk1_2(X1,X2) = X1
    | X2 = k1_enumset1(X1,X1,X1)
    | r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_23]),c_0_24])).

cnf(c_0_44,negated_conjecture,
    ( k1_relat_1(X1) != esk6_0
    | ~ r2_hidden(X2,k2_relat_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_34]),c_0_39]),c_0_40])).

cnf(c_0_45,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_41])])).

cnf(c_0_46,plain,
    ( X1 = X2
    | ~ r2_hidden(X3,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_19])).

cnf(c_0_47,plain,
    ( X1 = X2
    | ~ r2_hidden(esk2_3(esk5_2(X3,X2),k2_relat_1(esk5_2(X3,X2)),X1),X3)
    | ~ r2_hidden(X1,k2_relat_1(esk5_2(X3,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_42]),c_0_21]),c_0_11])])).

cnf(c_0_48,plain,
    ( r2_hidden(esk2_3(esk5_2(X1,X2),k2_relat_1(esk5_2(X1,X2)),X3),X1)
    | ~ r2_hidden(X3,k2_relat_1(esk5_2(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_10]),c_0_21]),c_0_11])])).

cnf(c_0_49,negated_conjecture,
    ( esk1_2(esk7_0,k2_relat_1(X1)) = esk7_0
    | r2_hidden(esk1_2(esk7_0,k2_relat_1(X1)),k2_relat_1(X1))
    | k1_relat_1(X1) != esk6_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_43])])).

cnf(c_0_50,plain,
    ( r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_28]),c_0_29]),c_0_27])]),c_0_46])).

cnf(c_0_52,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_relat_1(esk5_2(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( esk1_2(esk7_0,k2_relat_1(esk5_2(esk6_0,X1))) = esk7_0
    | r2_hidden(esk1_2(esk7_0,k2_relat_1(esk5_2(esk6_0,X1))),k2_relat_1(esk5_2(esk6_0,X1))) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_10]),c_0_21]),c_0_11])])])).

cnf(c_0_54,plain,
    ( X1 = k2_relat_1(k1_xboole_0)
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_28]),c_0_27]),c_0_29])]),c_0_51])).

cnf(c_0_55,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_56,negated_conjecture,
    ( esk1_2(esk7_0,k2_relat_1(esk5_2(esk6_0,X1))) = esk7_0
    | esk1_2(esk7_0,k2_relat_1(esk5_2(esk6_0,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_54])).

cnf(c_0_58,plain,
    ( X2 = k1_enumset1(X1,X1,X1)
    | esk1_2(X1,X2) != X1
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_23]),c_0_24])).

cnf(c_0_59,negated_conjecture,
    ( esk1_2(esk7_0,k2_relat_1(esk5_2(esk6_0,esk7_0))) = esk7_0 ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_56])])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,k2_relat_1(esk5_2(X2,X1)))
    | ~ r2_hidden(X3,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_13]),c_0_21]),c_0_11]),c_0_10])])).

cnf(c_0_61,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[c_0_54,c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( k1_enumset1(esk7_0,esk7_0,esk7_0) = k2_relat_1(esk5_2(esk6_0,esk7_0))
    | ~ r2_hidden(esk7_0,k2_relat_1(esk5_2(esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k2_relat_1(esk5_2(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_65,negated_conjecture,
    ( k1_enumset1(esk7_0,esk7_0,esk7_0) = k2_relat_1(esk5_2(esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_66,negated_conjecture,
    ( k2_relat_1(X1) != k2_relat_1(esk5_2(esk6_0,esk7_0))
    | k1_relat_1(X1) != esk6_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_32,c_0_65])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_66]),c_0_10]),c_0_21]),c_0_11])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:27:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.48  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.18/0.48  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.18/0.48  #
% 0.18/0.48  # Preprocessing time       : 0.027 s
% 0.18/0.48  # Presaturation interreduction done
% 0.18/0.48  
% 0.18/0.48  # Proof found!
% 0.18/0.48  # SZS status Theorem
% 0.18/0.48  # SZS output start CNFRefutation
% 0.18/0.48  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 0.18/0.48  fof(s3_funct_1__e2_24__funct_1, axiom, ![X1, X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&![X4]:(r2_hidden(X4,X1)=>k1_funct_1(X3,X4)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 0.18/0.48  fof(t15_funct_1, conjecture, ![X1]:(X1!=k1_xboole_0=>![X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&k2_relat_1(X3)=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_funct_1)).
% 0.18/0.48  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.18/0.48  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.18/0.48  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.18/0.48  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.18/0.48  fof(c_0_7, plain, ![X15]:((k1_relat_1(X15)!=k1_xboole_0|X15=k1_xboole_0|~v1_relat_1(X15))&(k2_relat_1(X15)!=k1_xboole_0|X15=k1_xboole_0|~v1_relat_1(X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.18/0.48  fof(c_0_8, plain, ![X26, X27, X29]:(((v1_relat_1(esk5_2(X26,X27))&v1_funct_1(esk5_2(X26,X27)))&k1_relat_1(esk5_2(X26,X27))=X26)&(~r2_hidden(X29,X26)|k1_funct_1(esk5_2(X26,X27),X29)=X27)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).
% 0.18/0.48  cnf(c_0_9, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.48  cnf(c_0_10, plain, (k1_relat_1(esk5_2(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.48  cnf(c_0_11, plain, (v1_relat_1(esk5_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.48  fof(c_0_12, negated_conjecture, ~(![X1]:(X1!=k1_xboole_0=>![X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&k2_relat_1(X3)=k1_tarski(X2)))), inference(assume_negation,[status(cth)],[t15_funct_1])).
% 0.18/0.48  cnf(c_0_13, plain, (k1_funct_1(esk5_2(X2,X3),X1)=X3|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.48  cnf(c_0_14, plain, (esk5_2(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11])])])).
% 0.18/0.48  fof(c_0_15, plain, ![X16, X17, X18, X20, X21, X22, X24]:((((r2_hidden(esk2_3(X16,X17,X18),k1_relat_1(X16))|~r2_hidden(X18,X17)|X17!=k2_relat_1(X16)|(~v1_relat_1(X16)|~v1_funct_1(X16)))&(X18=k1_funct_1(X16,esk2_3(X16,X17,X18))|~r2_hidden(X18,X17)|X17!=k2_relat_1(X16)|(~v1_relat_1(X16)|~v1_funct_1(X16))))&(~r2_hidden(X21,k1_relat_1(X16))|X20!=k1_funct_1(X16,X21)|r2_hidden(X20,X17)|X17!=k2_relat_1(X16)|(~v1_relat_1(X16)|~v1_funct_1(X16))))&((~r2_hidden(esk3_2(X16,X22),X22)|(~r2_hidden(X24,k1_relat_1(X16))|esk3_2(X16,X22)!=k1_funct_1(X16,X24))|X22=k2_relat_1(X16)|(~v1_relat_1(X16)|~v1_funct_1(X16)))&((r2_hidden(esk4_2(X16,X22),k1_relat_1(X16))|r2_hidden(esk3_2(X16,X22),X22)|X22=k2_relat_1(X16)|(~v1_relat_1(X16)|~v1_funct_1(X16)))&(esk3_2(X16,X22)=k1_funct_1(X16,esk4_2(X16,X22))|r2_hidden(esk3_2(X16,X22),X22)|X22=k2_relat_1(X16)|(~v1_relat_1(X16)|~v1_funct_1(X16)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.18/0.48  fof(c_0_16, negated_conjecture, ![X32]:(esk6_0!=k1_xboole_0&(~v1_relat_1(X32)|~v1_funct_1(X32)|k1_relat_1(X32)!=esk6_0|k2_relat_1(X32)!=k1_tarski(esk7_0))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).
% 0.18/0.48  fof(c_0_17, plain, ![X12]:k2_tarski(X12,X12)=k1_tarski(X12), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.18/0.48  fof(c_0_18, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.18/0.48  cnf(c_0_19, plain, (k1_funct_1(k1_xboole_0,X1)=X2|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.18/0.48  cnf(c_0_20, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.48  cnf(c_0_21, plain, (v1_funct_1(esk5_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.48  cnf(c_0_22, negated_conjecture, (~v1_relat_1(X1)|~v1_funct_1(X1)|k1_relat_1(X1)!=esk6_0|k2_relat_1(X1)!=k1_tarski(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.48  cnf(c_0_23, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.48  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.48  cnf(c_0_25, plain, (v1_relat_1(k1_funct_1(k1_xboole_0,X1))|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_11, c_0_19])).
% 0.18/0.48  cnf(c_0_26, plain, (r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_20])).
% 0.18/0.48  cnf(c_0_27, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_10, c_0_14])).
% 0.18/0.48  cnf(c_0_28, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_14])).
% 0.18/0.48  cnf(c_0_29, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_11, c_0_14])).
% 0.18/0.48  cnf(c_0_30, plain, (v1_funct_1(k1_funct_1(k1_xboole_0,X1))|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_19])).
% 0.18/0.48  fof(c_0_31, plain, ![X5, X6, X7, X8, X9, X10]:(((~r2_hidden(X7,X6)|X7=X5|X6!=k1_tarski(X5))&(X8!=X5|r2_hidden(X8,X6)|X6!=k1_tarski(X5)))&((~r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)!=X9|X10=k1_tarski(X9))&(r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)=X9|X10=k1_tarski(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.18/0.48  cnf(c_0_32, negated_conjecture, (k1_relat_1(X1)!=esk6_0|k2_relat_1(X1)!=k1_enumset1(esk7_0,esk7_0,esk7_0)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 0.18/0.48  cnf(c_0_33, plain, (v1_relat_1(X1)|~r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_25, c_0_19])).
% 0.18/0.48  cnf(c_0_34, plain, (r2_hidden(esk2_3(k1_xboole_0,k2_relat_1(k1_xboole_0),X1),k1_xboole_0)|~r2_hidden(X1,k2_relat_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])])).
% 0.18/0.48  cnf(c_0_35, plain, (v1_funct_1(X1)|~r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_19])).
% 0.18/0.48  cnf(c_0_36, plain, (X1=k1_funct_1(X2,esk2_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.48  cnf(c_0_37, plain, (r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.48  cnf(c_0_38, negated_conjecture, (k1_relat_1(X1)!=esk6_0|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_19]), c_0_19])).
% 0.18/0.48  cnf(c_0_39, plain, (v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.18/0.48  cnf(c_0_40, plain, (v1_funct_1(X1)|~r2_hidden(X2,k2_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_35, c_0_34])).
% 0.18/0.48  cnf(c_0_41, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.48  cnf(c_0_42, plain, (k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_36])).
% 0.18/0.48  cnf(c_0_43, plain, (esk1_2(X1,X2)=X1|X2=k1_enumset1(X1,X1,X1)|r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_23]), c_0_24])).
% 0.18/0.48  cnf(c_0_44, negated_conjecture, (k1_relat_1(X1)!=esk6_0|~r2_hidden(X2,k2_relat_1(k1_xboole_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_34]), c_0_39]), c_0_40])).
% 0.18/0.48  cnf(c_0_45, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_41])])).
% 0.18/0.48  cnf(c_0_46, plain, (X1=X2|~r2_hidden(X3,k1_xboole_0)), inference(spm,[status(thm)],[c_0_19, c_0_19])).
% 0.18/0.48  cnf(c_0_47, plain, (X1=X2|~r2_hidden(esk2_3(esk5_2(X3,X2),k2_relat_1(esk5_2(X3,X2)),X1),X3)|~r2_hidden(X1,k2_relat_1(esk5_2(X3,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_42]), c_0_21]), c_0_11])])).
% 0.18/0.48  cnf(c_0_48, plain, (r2_hidden(esk2_3(esk5_2(X1,X2),k2_relat_1(esk5_2(X1,X2)),X3),X1)|~r2_hidden(X3,k2_relat_1(esk5_2(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_10]), c_0_21]), c_0_11])])).
% 0.18/0.48  cnf(c_0_49, negated_conjecture, (esk1_2(esk7_0,k2_relat_1(X1))=esk7_0|r2_hidden(esk1_2(esk7_0,k2_relat_1(X1)),k2_relat_1(X1))|k1_relat_1(X1)!=esk6_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_43])])).
% 0.18/0.48  cnf(c_0_50, plain, (r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))|r2_hidden(esk3_2(X1,X2),X2)|X2=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.48  cnf(c_0_51, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_28]), c_0_29]), c_0_27])]), c_0_46])).
% 0.18/0.48  cnf(c_0_52, plain, (X1=X2|~r2_hidden(X1,k2_relat_1(esk5_2(X3,X2)))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.18/0.48  cnf(c_0_53, negated_conjecture, (esk1_2(esk7_0,k2_relat_1(esk5_2(esk6_0,X1)))=esk7_0|r2_hidden(esk1_2(esk7_0,k2_relat_1(esk5_2(esk6_0,X1))),k2_relat_1(esk5_2(esk6_0,X1)))), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_10]), c_0_21]), c_0_11])])])).
% 0.18/0.48  cnf(c_0_54, plain, (X1=k2_relat_1(k1_xboole_0)|r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_28]), c_0_27]), c_0_29])]), c_0_51])).
% 0.18/0.48  cnf(c_0_55, plain, (X2=k1_tarski(X1)|~r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.48  cnf(c_0_56, negated_conjecture, (esk1_2(esk7_0,k2_relat_1(esk5_2(esk6_0,X1)))=esk7_0|esk1_2(esk7_0,k2_relat_1(esk5_2(esk6_0,X1)))=X1), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.18/0.48  cnf(c_0_57, negated_conjecture, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_54])).
% 0.18/0.48  cnf(c_0_58, plain, (X2=k1_enumset1(X1,X1,X1)|esk1_2(X1,X2)!=X1|~r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_23]), c_0_24])).
% 0.18/0.48  cnf(c_0_59, negated_conjecture, (esk1_2(esk7_0,k2_relat_1(esk5_2(esk6_0,esk7_0)))=esk7_0), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_56])])).
% 0.18/0.48  cnf(c_0_60, plain, (r2_hidden(X1,k2_relat_1(esk5_2(X2,X1)))|~r2_hidden(X3,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_13]), c_0_21]), c_0_11]), c_0_10])])).
% 0.18/0.48  cnf(c_0_61, plain, (X1=k1_xboole_0|r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[c_0_54, c_0_57])).
% 0.18/0.48  cnf(c_0_62, negated_conjecture, (k1_enumset1(esk7_0,esk7_0,esk7_0)=k2_relat_1(esk5_2(esk6_0,esk7_0))|~r2_hidden(esk7_0,k2_relat_1(esk5_2(esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.18/0.48  cnf(c_0_63, plain, (X1=k1_xboole_0|r2_hidden(X2,k2_relat_1(esk5_2(X1,X2)))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.18/0.48  cnf(c_0_64, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.48  cnf(c_0_65, negated_conjecture, (k1_enumset1(esk7_0,esk7_0,esk7_0)=k2_relat_1(esk5_2(esk6_0,esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.18/0.48  cnf(c_0_66, negated_conjecture, (k2_relat_1(X1)!=k2_relat_1(esk5_2(esk6_0,esk7_0))|k1_relat_1(X1)!=esk6_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_32, c_0_65])).
% 0.18/0.48  cnf(c_0_67, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_66]), c_0_10]), c_0_21]), c_0_11])]), ['proof']).
% 0.18/0.48  # SZS output end CNFRefutation
% 0.18/0.48  # Proof object total steps             : 68
% 0.18/0.48  # Proof object clause steps            : 53
% 0.18/0.48  # Proof object formula steps           : 15
% 0.18/0.48  # Proof object conjectures             : 18
% 0.18/0.48  # Proof object clause conjectures      : 15
% 0.18/0.48  # Proof object formula conjectures     : 3
% 0.18/0.48  # Proof object initial clauses used    : 15
% 0.18/0.48  # Proof object initial formulas used   : 7
% 0.18/0.48  # Proof object generating inferences   : 30
% 0.18/0.48  # Proof object simplifying inferences  : 51
% 0.18/0.48  # Training examples: 0 positive, 0 negative
% 0.18/0.48  # Parsed axioms                        : 7
% 0.18/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.48  # Initial clauses                      : 20
% 0.18/0.48  # Removed in clause preprocessing      : 2
% 0.18/0.48  # Initial clauses in saturation        : 18
% 0.18/0.48  # Processed clauses                    : 438
% 0.18/0.48  # ...of these trivial                  : 4
% 0.18/0.48  # ...subsumed                          : 291
% 0.18/0.48  # ...remaining for further processing  : 143
% 0.18/0.48  # Other redundant clauses eliminated   : 114
% 0.18/0.48  # Clauses deleted for lack of memory   : 0
% 0.18/0.48  # Backward-subsumed                    : 7
% 0.18/0.48  # Backward-rewritten                   : 16
% 0.18/0.48  # Generated clauses                    : 4223
% 0.18/0.48  # ...of the previous two non-trivial   : 3741
% 0.18/0.48  # Contextual simplify-reflections      : 5
% 0.18/0.48  # Paramodulations                      : 4092
% 0.18/0.48  # Factorizations                       : 17
% 0.18/0.48  # Equation resolutions                 : 116
% 0.18/0.48  # Propositional unsat checks           : 0
% 0.18/0.48  #    Propositional check models        : 0
% 0.18/0.48  #    Propositional check unsatisfiable : 0
% 0.18/0.48  #    Propositional clauses             : 0
% 0.18/0.48  #    Propositional clauses after purity: 0
% 0.18/0.48  #    Propositional unsat core size     : 0
% 0.18/0.48  #    Propositional preprocessing time  : 0.000
% 0.18/0.48  #    Propositional encoding time       : 0.000
% 0.18/0.48  #    Propositional solver time         : 0.000
% 0.18/0.48  #    Success case prop preproc time    : 0.000
% 0.18/0.48  #    Success case prop encoding time   : 0.000
% 0.18/0.48  #    Success case prop solver time     : 0.000
% 0.18/0.48  # Current number of processed clauses  : 97
% 0.18/0.48  #    Positive orientable unit clauses  : 14
% 0.18/0.48  #    Positive unorientable unit clauses: 0
% 0.18/0.48  #    Negative unit clauses             : 2
% 0.18/0.48  #    Non-unit-clauses                  : 81
% 0.18/0.48  # Current number of unprocessed clauses: 3286
% 0.18/0.48  # ...number of literals in the above   : 21149
% 0.18/0.48  # Current number of archived formulas  : 0
% 0.18/0.48  # Current number of archived clauses   : 43
% 0.18/0.48  # Clause-clause subsumption calls (NU) : 3283
% 0.18/0.48  # Rec. Clause-clause subsumption calls : 1923
% 0.18/0.48  # Non-unit clause-clause subsumptions  : 251
% 0.18/0.48  # Unit Clause-clause subsumption calls : 102
% 0.18/0.48  # Rewrite failures with RHS unbound    : 0
% 0.18/0.48  # BW rewrite match attempts            : 28
% 0.18/0.48  # BW rewrite match successes           : 4
% 0.18/0.48  # Condensation attempts                : 0
% 0.18/0.48  # Condensation successes               : 0
% 0.18/0.48  # Termbank termtop insertions          : 97954
% 0.18/0.48  
% 0.18/0.48  # -------------------------------------------------
% 0.18/0.48  # User time                : 0.143 s
% 0.18/0.48  # System time              : 0.005 s
% 0.18/0.48  # Total time               : 0.148 s
% 0.18/0.48  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
