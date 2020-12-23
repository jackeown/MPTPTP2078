%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:08 EST 2020

% Result     : Theorem 20.59s
% Output     : CNFRefutation 20.59s
% Verified   : 
% Statistics : Number of formulae       :   66 (1184 expanded)
%              Number of clauses        :   51 ( 510 expanded)
%              Number of leaves         :    7 ( 323 expanded)
%              Depth                    :   20
%              Number of atoms          :  215 (4618 expanded)
%              Number of equality atoms :   62 (1699 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_funct_1,conjecture,(
    ! [X1,X2] :
      ~ ( ~ ( X1 = k1_xboole_0
            & X2 != k1_xboole_0 )
        & ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ~ ( X2 = k1_relat_1(X3)
                & r1_tarski(k2_relat_1(X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

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

fof(t12_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( ~ ( X1 = k1_xboole_0
              & X2 != k1_xboole_0 )
          & ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ~ ( X2 = k1_relat_1(X3)
                  & r1_tarski(k2_relat_1(X3),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_funct_1])).

fof(c_0_8,negated_conjecture,(
    ! [X32] :
      ( ( esk6_0 != k1_xboole_0
        | esk7_0 = k1_xboole_0 )
      & ( ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32)
        | esk7_0 != k1_relat_1(X32)
        | ~ r1_tarski(k2_relat_1(X32),esk6_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

fof(c_0_9,plain,(
    ! [X24,X25,X27] :
      ( v1_relat_1(esk5_2(X24,X25))
      & v1_funct_1(esk5_2(X24,X25))
      & k1_relat_1(esk5_2(X24,X25)) = X24
      & ( ~ r2_hidden(X27,X24)
        | k1_funct_1(esk5_2(X24,X25),X27) = X25 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).

cnf(c_0_10,negated_conjecture,
    ( ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | esk7_0 != k1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( k1_relat_1(esk5_2(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( v1_funct_1(esk5_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( v1_relat_1(esk5_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_15,plain,(
    ! [X13] :
      ( ( k1_relat_1(X13) != k1_xboole_0
        | k2_relat_1(X13) = k1_xboole_0
        | ~ v1_relat_1(X13) )
      & ( k2_relat_1(X13) != k1_xboole_0
        | k1_relat_1(X13) = k1_xboole_0
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

fof(c_0_16,plain,(
    ! [X14,X15,X16,X18,X19,X20,X22] :
      ( ( r2_hidden(esk2_3(X14,X15,X16),k1_relat_1(X14))
        | ~ r2_hidden(X16,X15)
        | X15 != k2_relat_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( X16 = k1_funct_1(X14,esk2_3(X14,X15,X16))
        | ~ r2_hidden(X16,X15)
        | X15 != k2_relat_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( ~ r2_hidden(X19,k1_relat_1(X14))
        | X18 != k1_funct_1(X14,X19)
        | r2_hidden(X18,X15)
        | X15 != k2_relat_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( ~ r2_hidden(esk3_2(X14,X20),X20)
        | ~ r2_hidden(X22,k1_relat_1(X14))
        | esk3_2(X14,X20) != k1_funct_1(X14,X22)
        | X20 = k2_relat_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( r2_hidden(esk4_2(X14,X20),k1_relat_1(X14))
        | r2_hidden(esk3_2(X14,X20),X20)
        | X20 = k2_relat_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( esk3_2(X14,X20) = k1_funct_1(X14,esk4_2(X14,X20))
        | r2_hidden(esk3_2(X14,X20),X20)
        | X20 = k2_relat_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_17,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X29)
      | ~ v1_funct_1(X29)
      | ~ r2_hidden(X28,k1_relat_1(X29))
      | r2_hidden(k1_funct_1(X29,X28),k2_relat_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).

cnf(c_0_18,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13])])])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k1_funct_1(esk5_2(X2,X3),X1) = X3
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0),k2_relat_1(esk5_2(esk7_0,X1))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( k2_relat_1(esk5_2(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_11]),c_0_13])])])).

cnf(c_0_26,plain,
    ( X1 = k2_relat_1(esk5_2(X2,X3))
    | r2_hidden(esk3_2(esk5_2(X2,X3),X1),X1)
    | r2_hidden(esk4_2(esk5_2(X2,X3),X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_12]),c_0_11]),c_0_13])])).

cnf(c_0_27,plain,
    ( r2_hidden(k1_funct_1(esk5_2(X1,X2),X3),k2_relat_1(esk5_2(X1,X2)))
    | ~ r2_hidden(X3,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_12]),c_0_13]),c_0_11])])).

cnf(c_0_28,negated_conjecture,
    ( k1_funct_1(esk5_2(k2_relat_1(esk5_2(esk7_0,X1)),X2),esk1_2(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0)) = X2 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_2(esk5_2(k1_xboole_0,X2),X1),k1_xboole_0)
    | r2_hidden(esk3_2(esk5_2(k1_xboole_0,X2),X1),X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(esk5_2(k2_relat_1(esk5_2(esk7_0,X2)),X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_24]),c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk3_2(esk5_2(k1_xboole_0,X1),esk6_0),esk6_0)
    | r2_hidden(esk4_2(esk5_2(k1_xboole_0,X1),esk6_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk4_2(esk5_2(k1_xboole_0,X1),esk6_0),k1_xboole_0)
    | r2_hidden(esk3_2(esk5_2(k1_xboole_0,X1),esk6_0),esk6_0)
    | r2_hidden(X2,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_25]),c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk4_2(esk5_2(k1_xboole_0,X1),esk6_0),k1_xboole_0)
    | r2_hidden(esk3_2(esk5_2(k1_xboole_0,X1),esk6_0),esk6_0) ),
    inference(ef,[status(thm)],[c_0_33])).

cnf(c_0_35,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_2(k1_xboole_0,X1),esk4_2(esk5_2(k1_xboole_0,X2),esk6_0)),k1_xboole_0)
    | r2_hidden(esk3_2(esk5_2(k1_xboole_0,X2),esk6_0),esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_34]),c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( k1_funct_1(esk5_2(k1_xboole_0,X1),esk4_2(esk5_2(k1_xboole_0,X2),esk6_0)) = X1
    | r2_hidden(esk3_2(esk5_2(k1_xboole_0,X2),esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_34])).

cnf(c_0_38,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_19])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk3_2(esk5_2(k1_xboole_0,X1),esk6_0),esk6_0)
    | r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk3_2(esk5_2(k1_xboole_0,X1),esk6_0),X2)
    | r2_hidden(esk1_2(esk6_0,X2),esk6_0)
    | r2_hidden(X3,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_41,plain,
    ( X1 = k1_funct_1(X2,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk3_2(esk5_2(k1_xboole_0,X1),esk6_0),k1_xboole_0)
    | r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0) ),
    inference(ef,[status(thm)],[c_0_40])).

cnf(c_0_43,plain,
    ( k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_44,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_2(k1_xboole_0,X1),esk3_2(esk5_2(k1_xboole_0,X2),esk6_0)),k1_xboole_0)
    | r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_42]),c_0_25])).

cnf(c_0_46,negated_conjecture,
    ( k1_funct_1(esk5_2(k1_xboole_0,X1),esk3_2(esk5_2(k1_xboole_0,X2),esk6_0)) = X1
    | r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_42])).

cnf(c_0_47,plain,
    ( k1_funct_1(esk5_2(X1,X2),esk2_3(esk5_2(X1,X2),k2_relat_1(esk5_2(X1,X2)),X3)) = X3
    | ~ r2_hidden(X3,k2_relat_1(esk5_2(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_12]),c_0_13])])).

cnf(c_0_48,plain,
    ( r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0)
    | r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,plain,
    ( k1_funct_1(esk5_2(k1_xboole_0,X1),esk2_3(esk5_2(k1_xboole_0,X1),k1_xboole_0,X2)) = X2
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_25])).

cnf(c_0_51,plain,
    ( r2_hidden(esk2_3(esk5_2(X1,X2),k2_relat_1(esk5_2(X1,X2)),X3),X1)
    | ~ r2_hidden(X3,k2_relat_1(esk5_2(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_12]),c_0_11]),c_0_13])])).

cnf(c_0_52,negated_conjecture,
    ( k1_funct_1(esk5_2(k1_xboole_0,X1),X2) = X1
    | r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( k1_funct_1(esk5_2(k1_xboole_0,X1),esk2_3(esk5_2(k1_xboole_0,X1),k1_xboole_0,X2)) = X2
    | r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_49])).

fof(c_0_54,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk2_3(esk5_2(esk7_0,X1),k2_relat_1(esk5_2(esk7_0,X1)),esk1_2(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_24])).

cnf(c_0_56,negated_conjecture,
    ( X1 = X2
    | r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( k1_funct_1(esk5_2(esk7_0,X1),esk2_3(esk5_2(esk7_0,X2),k2_relat_1(esk5_2(esk7_0,X2)),esk1_2(k2_relat_1(esk5_2(esk7_0,X2)),esk6_0))) = X1 ),
    inference(spm,[status(thm)],[c_0_23,c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0)
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_56])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_62,negated_conjecture,
    ( esk1_2(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_24]),c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_18])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_63,c_0_64]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:57:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 20.59/20.76  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 20.59/20.76  # and selection function SelectCQIArEqFirst.
% 20.59/20.76  #
% 20.59/20.76  # Preprocessing time       : 0.027 s
% 20.59/20.76  # Presaturation interreduction done
% 20.59/20.76  
% 20.59/20.76  # Proof found!
% 20.59/20.76  # SZS status Theorem
% 20.59/20.76  # SZS output start CNFRefutation
% 20.59/20.76  fof(t18_funct_1, conjecture, ![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 20.59/20.76  fof(s3_funct_1__e2_24__funct_1, axiom, ![X1, X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&![X4]:(r2_hidden(X4,X1)=>k1_funct_1(X3,X4)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 20.59/20.76  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 20.59/20.76  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 20.59/20.76  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 20.59/20.76  fof(t12_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 20.59/20.76  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 20.59/20.76  fof(c_0_7, negated_conjecture, ~(![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1))))))), inference(assume_negation,[status(cth)],[t18_funct_1])).
% 20.59/20.76  fof(c_0_8, negated_conjecture, ![X32]:((esk6_0!=k1_xboole_0|esk7_0=k1_xboole_0)&(~v1_relat_1(X32)|~v1_funct_1(X32)|(esk7_0!=k1_relat_1(X32)|~r1_tarski(k2_relat_1(X32),esk6_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).
% 20.59/20.76  fof(c_0_9, plain, ![X24, X25, X27]:(((v1_relat_1(esk5_2(X24,X25))&v1_funct_1(esk5_2(X24,X25)))&k1_relat_1(esk5_2(X24,X25))=X24)&(~r2_hidden(X27,X24)|k1_funct_1(esk5_2(X24,X25),X27)=X25)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).
% 20.59/20.76  cnf(c_0_10, negated_conjecture, (~v1_relat_1(X1)|~v1_funct_1(X1)|esk7_0!=k1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 20.59/20.76  cnf(c_0_11, plain, (k1_relat_1(esk5_2(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_9])).
% 20.59/20.76  cnf(c_0_12, plain, (v1_funct_1(esk5_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 20.59/20.76  cnf(c_0_13, plain, (v1_relat_1(esk5_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 20.59/20.76  fof(c_0_14, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 20.59/20.76  fof(c_0_15, plain, ![X13]:((k1_relat_1(X13)!=k1_xboole_0|k2_relat_1(X13)=k1_xboole_0|~v1_relat_1(X13))&(k2_relat_1(X13)!=k1_xboole_0|k1_relat_1(X13)=k1_xboole_0|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 20.59/20.76  fof(c_0_16, plain, ![X14, X15, X16, X18, X19, X20, X22]:((((r2_hidden(esk2_3(X14,X15,X16),k1_relat_1(X14))|~r2_hidden(X16,X15)|X15!=k2_relat_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14)))&(X16=k1_funct_1(X14,esk2_3(X14,X15,X16))|~r2_hidden(X16,X15)|X15!=k2_relat_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))))&(~r2_hidden(X19,k1_relat_1(X14))|X18!=k1_funct_1(X14,X19)|r2_hidden(X18,X15)|X15!=k2_relat_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))))&((~r2_hidden(esk3_2(X14,X20),X20)|(~r2_hidden(X22,k1_relat_1(X14))|esk3_2(X14,X20)!=k1_funct_1(X14,X22))|X20=k2_relat_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14)))&((r2_hidden(esk4_2(X14,X20),k1_relat_1(X14))|r2_hidden(esk3_2(X14,X20),X20)|X20=k2_relat_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14)))&(esk3_2(X14,X20)=k1_funct_1(X14,esk4_2(X14,X20))|r2_hidden(esk3_2(X14,X20),X20)|X20=k2_relat_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 20.59/20.76  fof(c_0_17, plain, ![X28, X29]:(~v1_relat_1(X29)|~v1_funct_1(X29)|(~r2_hidden(X28,k1_relat_1(X29))|r2_hidden(k1_funct_1(X29,X28),k2_relat_1(X29)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).
% 20.59/20.76  cnf(c_0_18, negated_conjecture, (~r1_tarski(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12]), c_0_13])])])).
% 20.59/20.76  cnf(c_0_19, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 20.59/20.76  cnf(c_0_20, plain, (k2_relat_1(X1)=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 20.59/20.76  cnf(c_0_21, plain, (r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))|r2_hidden(esk3_2(X1,X2),X2)|X2=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 20.59/20.76  cnf(c_0_22, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 20.59/20.76  cnf(c_0_23, plain, (k1_funct_1(esk5_2(X2,X3),X1)=X3|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 20.59/20.76  cnf(c_0_24, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0),k2_relat_1(esk5_2(esk7_0,X1)))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 20.59/20.76  cnf(c_0_25, plain, (k2_relat_1(esk5_2(k1_xboole_0,X1))=k1_xboole_0), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_11]), c_0_13])])])).
% 20.59/20.76  cnf(c_0_26, plain, (X1=k2_relat_1(esk5_2(X2,X3))|r2_hidden(esk3_2(esk5_2(X2,X3),X1),X1)|r2_hidden(esk4_2(esk5_2(X2,X3),X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_12]), c_0_11]), c_0_13])])).
% 20.59/20.76  cnf(c_0_27, plain, (r2_hidden(k1_funct_1(esk5_2(X1,X2),X3),k2_relat_1(esk5_2(X1,X2)))|~r2_hidden(X3,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_12]), c_0_13]), c_0_11])])).
% 20.59/20.76  cnf(c_0_28, negated_conjecture, (k1_funct_1(esk5_2(k2_relat_1(esk5_2(esk7_0,X1)),X2),esk1_2(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0))=X2), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 20.59/20.76  cnf(c_0_29, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 20.59/20.76  cnf(c_0_30, plain, (X1=k1_xboole_0|r2_hidden(esk4_2(esk5_2(k1_xboole_0,X2),X1),k1_xboole_0)|r2_hidden(esk3_2(esk5_2(k1_xboole_0,X2),X1),X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 20.59/20.76  cnf(c_0_31, negated_conjecture, (r2_hidden(X1,k2_relat_1(esk5_2(k2_relat_1(esk5_2(esk7_0,X2)),X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_24]), c_0_28])).
% 20.59/20.76  cnf(c_0_32, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk3_2(esk5_2(k1_xboole_0,X1),esk6_0),esk6_0)|r2_hidden(esk4_2(esk5_2(k1_xboole_0,X1),esk6_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 20.59/20.76  cnf(c_0_33, negated_conjecture, (r2_hidden(esk4_2(esk5_2(k1_xboole_0,X1),esk6_0),k1_xboole_0)|r2_hidden(esk3_2(esk5_2(k1_xboole_0,X1),esk6_0),esk6_0)|r2_hidden(X2,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_25]), c_0_25])).
% 20.59/20.76  cnf(c_0_34, negated_conjecture, (r2_hidden(esk4_2(esk5_2(k1_xboole_0,X1),esk6_0),k1_xboole_0)|r2_hidden(esk3_2(esk5_2(k1_xboole_0,X1),esk6_0),esk6_0)), inference(ef,[status(thm)],[c_0_33])).
% 20.59/20.76  cnf(c_0_35, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 20.59/20.76  cnf(c_0_36, negated_conjecture, (r2_hidden(k1_funct_1(esk5_2(k1_xboole_0,X1),esk4_2(esk5_2(k1_xboole_0,X2),esk6_0)),k1_xboole_0)|r2_hidden(esk3_2(esk5_2(k1_xboole_0,X2),esk6_0),esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_34]), c_0_25])).
% 20.59/20.76  cnf(c_0_37, negated_conjecture, (k1_funct_1(esk5_2(k1_xboole_0,X1),esk4_2(esk5_2(k1_xboole_0,X2),esk6_0))=X1|r2_hidden(esk3_2(esk5_2(k1_xboole_0,X2),esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_23, c_0_34])).
% 20.59/20.76  cnf(c_0_38, plain, (r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_35, c_0_19])).
% 20.59/20.76  cnf(c_0_39, negated_conjecture, (r2_hidden(esk3_2(esk5_2(k1_xboole_0,X1),esk6_0),esk6_0)|r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 20.59/20.76  cnf(c_0_40, negated_conjecture, (r2_hidden(esk3_2(esk5_2(k1_xboole_0,X1),esk6_0),X2)|r2_hidden(esk1_2(esk6_0,X2),esk6_0)|r2_hidden(X3,k1_xboole_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 20.59/20.76  cnf(c_0_41, plain, (X1=k1_funct_1(X2,esk2_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 20.59/20.76  cnf(c_0_42, negated_conjecture, (r2_hidden(esk3_2(esk5_2(k1_xboole_0,X1),esk6_0),k1_xboole_0)|r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0)), inference(ef,[status(thm)],[c_0_40])).
% 20.59/20.76  cnf(c_0_43, plain, (k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_41])).
% 20.59/20.76  cnf(c_0_44, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 20.59/20.76  cnf(c_0_45, negated_conjecture, (r2_hidden(k1_funct_1(esk5_2(k1_xboole_0,X1),esk3_2(esk5_2(k1_xboole_0,X2),esk6_0)),k1_xboole_0)|r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_42]), c_0_25])).
% 20.59/20.76  cnf(c_0_46, negated_conjecture, (k1_funct_1(esk5_2(k1_xboole_0,X1),esk3_2(esk5_2(k1_xboole_0,X2),esk6_0))=X1|r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0)), inference(spm,[status(thm)],[c_0_23, c_0_42])).
% 20.59/20.76  cnf(c_0_47, plain, (k1_funct_1(esk5_2(X1,X2),esk2_3(esk5_2(X1,X2),k2_relat_1(esk5_2(X1,X2)),X3))=X3|~r2_hidden(X3,k2_relat_1(esk5_2(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_12]), c_0_13])])).
% 20.59/20.76  cnf(c_0_48, plain, (r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_44])).
% 20.59/20.76  cnf(c_0_49, negated_conjecture, (r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0)|r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 20.59/20.76  cnf(c_0_50, plain, (k1_funct_1(esk5_2(k1_xboole_0,X1),esk2_3(esk5_2(k1_xboole_0,X1),k1_xboole_0,X2))=X2|~r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_47, c_0_25])).
% 20.59/20.76  cnf(c_0_51, plain, (r2_hidden(esk2_3(esk5_2(X1,X2),k2_relat_1(esk5_2(X1,X2)),X3),X1)|~r2_hidden(X3,k2_relat_1(esk5_2(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_12]), c_0_11]), c_0_13])])).
% 20.59/20.76  cnf(c_0_52, negated_conjecture, (k1_funct_1(esk5_2(k1_xboole_0,X1),X2)=X1|r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0)), inference(spm,[status(thm)],[c_0_23, c_0_49])).
% 20.59/20.76  cnf(c_0_53, negated_conjecture, (k1_funct_1(esk5_2(k1_xboole_0,X1),esk2_3(esk5_2(k1_xboole_0,X1),k1_xboole_0,X2))=X2|r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0)), inference(spm,[status(thm)],[c_0_50, c_0_49])).
% 20.59/20.76  fof(c_0_54, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 20.59/20.76  cnf(c_0_55, negated_conjecture, (r2_hidden(esk2_3(esk5_2(esk7_0,X1),k2_relat_1(esk5_2(esk7_0,X1)),esk1_2(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0)),esk7_0)), inference(spm,[status(thm)],[c_0_51, c_0_24])).
% 20.59/20.76  cnf(c_0_56, negated_conjecture, (X1=X2|r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 20.59/20.76  cnf(c_0_57, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_54])).
% 20.59/20.76  cnf(c_0_58, negated_conjecture, (k1_funct_1(esk5_2(esk7_0,X1),esk2_3(esk5_2(esk7_0,X2),k2_relat_1(esk5_2(esk7_0,X2)),esk1_2(k2_relat_1(esk5_2(esk7_0,X2)),esk6_0)))=X1), inference(spm,[status(thm)],[c_0_23, c_0_55])).
% 20.59/20.76  cnf(c_0_59, negated_conjecture, (r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0)|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_18, c_0_56])).
% 20.59/20.76  cnf(c_0_60, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_57])).
% 20.59/20.76  cnf(c_0_61, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 20.59/20.76  cnf(c_0_62, negated_conjecture, (esk1_2(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_24]), c_0_58])).
% 20.59/20.76  cnf(c_0_63, negated_conjecture, (r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 20.59/20.76  cnf(c_0_64, negated_conjecture, (~r2_hidden(X1,esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_18])).
% 20.59/20.76  cnf(c_0_65, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_63, c_0_64]), ['proof']).
% 20.59/20.76  # SZS output end CNFRefutation
% 20.59/20.76  # Proof object total steps             : 66
% 20.59/20.76  # Proof object clause steps            : 51
% 20.59/20.76  # Proof object formula steps           : 15
% 20.59/20.76  # Proof object conjectures             : 30
% 20.59/20.76  # Proof object clause conjectures      : 27
% 20.59/20.76  # Proof object formula conjectures     : 3
% 20.59/20.76  # Proof object initial clauses used    : 15
% 20.59/20.76  # Proof object initial formulas used   : 7
% 20.59/20.76  # Proof object generating inferences   : 32
% 20.59/20.76  # Proof object simplifying inferences  : 29
% 20.59/20.76  # Training examples: 0 positive, 0 negative
% 20.59/20.76  # Parsed axioms                        : 7
% 20.59/20.76  # Removed by relevancy pruning/SinE    : 0
% 20.59/20.76  # Initial clauses                      : 21
% 20.59/20.76  # Removed in clause preprocessing      : 0
% 20.59/20.76  # Initial clauses in saturation        : 21
% 20.59/20.76  # Processed clauses                    : 11195
% 20.59/20.76  # ...of these trivial                  : 170
% 20.59/20.76  # ...subsumed                          : 7999
% 20.59/20.76  # ...remaining for further processing  : 3026
% 20.59/20.76  # Other redundant clauses eliminated   : 50081
% 20.59/20.76  # Clauses deleted for lack of memory   : 0
% 20.59/20.76  # Backward-subsumed                    : 737
% 20.59/20.76  # Backward-rewritten                   : 114
% 20.59/20.76  # Generated clauses                    : 2156139
% 20.59/20.76  # ...of the previous two non-trivial   : 1775994
% 20.59/20.76  # Contextual simplify-reflections      : 130
% 20.59/20.76  # Paramodulations                      : 2104885
% 20.59/20.76  # Factorizations                       : 652
% 20.59/20.76  # Equation resolutions                 : 50081
% 20.59/20.76  # Propositional unsat checks           : 0
% 20.59/20.76  #    Propositional check models        : 0
% 20.59/20.76  #    Propositional check unsatisfiable : 0
% 20.59/20.76  #    Propositional clauses             : 0
% 20.59/20.76  #    Propositional clauses after purity: 0
% 20.59/20.76  #    Propositional unsat core size     : 0
% 20.59/20.76  #    Propositional preprocessing time  : 0.000
% 20.59/20.76  #    Propositional encoding time       : 0.000
% 20.59/20.76  #    Propositional solver time         : 0.000
% 20.59/20.76  #    Success case prop preproc time    : 0.000
% 20.59/20.76  #    Success case prop encoding time   : 0.000
% 20.59/20.76  #    Success case prop solver time     : 0.000
% 20.59/20.76  # Current number of processed clauses  : 1629
% 20.59/20.76  #    Positive orientable unit clauses  : 32
% 20.59/20.76  #    Positive unorientable unit clauses: 0
% 20.59/20.76  #    Negative unit clauses             : 2
% 20.59/20.76  #    Non-unit-clauses                  : 1595
% 20.59/20.76  # Current number of unprocessed clauses: 1756104
% 20.59/20.76  # ...number of literals in the above   : 11998137
% 20.59/20.76  # Current number of archived formulas  : 0
% 20.59/20.76  # Current number of archived clauses   : 1392
% 20.59/20.76  # Clause-clause subsumption calls (NU) : 1345525
% 20.59/20.76  # Rec. Clause-clause subsumption calls : 90936
% 20.59/20.76  # Non-unit clause-clause subsumptions  : 8844
% 20.59/20.76  # Unit Clause-clause subsumption calls : 2455
% 20.59/20.76  # Rewrite failures with RHS unbound    : 0
% 20.59/20.76  # BW rewrite match attempts            : 292
% 20.59/20.76  # BW rewrite match successes           : 33
% 20.59/20.76  # Condensation attempts                : 0
% 20.59/20.76  # Condensation successes               : 0
% 20.59/20.76  # Termbank termtop insertions          : 76693068
% 20.66/20.83  
% 20.66/20.83  # -------------------------------------------------
% 20.66/20.83  # User time                : 19.769 s
% 20.66/20.83  # System time              : 0.714 s
% 20.66/20.83  # Total time               : 20.483 s
% 20.66/20.83  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
