%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0619+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:55 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   34 ( 178 expanded)
%              Number of clauses        :   27 (  69 expanded)
%              Number of leaves         :    3 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :  132 ( 902 expanded)
%              Number of equality atoms :   53 ( 367 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t14_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(c_0_3,plain,(
    ! [X12,X13,X14,X16,X17,X18,X20] :
      ( ( r2_hidden(esk2_3(X12,X13,X14),k1_relat_1(X12))
        | ~ r2_hidden(X14,X13)
        | X13 != k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( X14 = k1_funct_1(X12,esk2_3(X12,X13,X14))
        | ~ r2_hidden(X14,X13)
        | X13 != k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( ~ r2_hidden(X17,k1_relat_1(X12))
        | X16 != k1_funct_1(X12,X17)
        | r2_hidden(X16,X13)
        | X13 != k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( ~ r2_hidden(esk3_2(X12,X18),X18)
        | ~ r2_hidden(X20,k1_relat_1(X12))
        | esk3_2(X12,X18) != k1_funct_1(X12,X20)
        | X18 = k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( r2_hidden(esk4_2(X12,X18),k1_relat_1(X12))
        | r2_hidden(esk3_2(X12,X18),X18)
        | X18 = k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( esk3_2(X12,X18) = k1_funct_1(X12,esk4_2(X12,X18))
        | r2_hidden(esk3_2(X12,X18),X18)
        | X18 = k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( k1_relat_1(X2) = k1_tarski(X1)
         => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t14_funct_1])).

fof(c_0_5,plain,(
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

cnf(c_0_6,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_funct_1(esk6_0)
    & k1_relat_1(esk6_0) = k1_tarski(esk5_0)
    & k2_relat_1(esk6_0) != k1_tarski(k1_funct_1(esk6_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_8,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( k1_relat_1(esk6_0) = k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( X1 = k1_funct_1(X2,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_14,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk2_3(esk6_0,k2_relat_1(esk6_0),X1),k1_tarski(esk5_0))
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12])])).

cnf(c_0_16,plain,
    ( k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( esk2_3(esk6_0,k2_relat_1(esk6_0),X1) = esk5_0
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_19,negated_conjecture,
    ( k1_funct_1(esk6_0,esk5_0) = X1
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_11]),c_0_12])])).

cnf(c_0_20,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_18])])).

cnf(c_0_21,negated_conjecture,
    ( k1_funct_1(esk6_0,esk5_0) = k1_funct_1(esk6_0,X1)
    | ~ r2_hidden(X1,k1_tarski(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_11]),c_0_12]),c_0_10])])).

cnf(c_0_22,negated_conjecture,
    ( k1_funct_1(esk6_0,esk2_3(esk6_0,k2_relat_1(esk6_0),X1)) = k1_funct_1(esk6_0,esk5_0)
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_15])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk6_0,esk5_0),k2_relat_1(esk6_0))
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_22]),c_0_11]),c_0_12]),c_0_10])]),c_0_15])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_26,negated_conjecture,
    ( esk1_2(X1,k2_relat_1(esk6_0)) = k1_funct_1(esk6_0,esk5_0)
    | esk1_2(X1,k2_relat_1(esk6_0)) = X1
    | k1_tarski(X1) = k2_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( k2_relat_1(esk6_0) != k1_tarski(k1_funct_1(esk6_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk6_0,esk5_0),k2_relat_1(esk6_0))
    | ~ r2_hidden(X1,k1_tarski(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_20]),c_0_11]),c_0_12]),c_0_10])])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_25])])).

cnf(c_0_30,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_31,negated_conjecture,
    ( esk1_2(k1_funct_1(esk6_0,esk5_0),k2_relat_1(esk6_0)) = k1_funct_1(esk6_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_26])]),c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk6_0,esk5_0),k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])]),c_0_27]),
    [proof]).

%------------------------------------------------------------------------------
