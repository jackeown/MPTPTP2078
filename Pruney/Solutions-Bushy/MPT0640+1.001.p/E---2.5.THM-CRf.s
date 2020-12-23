%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0640+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:57 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 162 expanded)
%              Number of clauses        :   28 (  52 expanded)
%              Number of leaves         :    6 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  174 ( 944 expanded)
%              Number of equality atoms :   31 (  58 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   23 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t47_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(k5_relat_1(X2,X1))
              & r1_tarski(k2_relat_1(X2),k1_relat_1(X1)) )
           => v2_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_1)).

fof(t46_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
           => k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(d8_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,k1_relat_1(X1))
              & r2_hidden(X3,k1_relat_1(X1))
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(t23_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(X2))
           => k1_funct_1(k5_relat_1(X2,X3),X1) = k1_funct_1(X3,k1_funct_1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

fof(fc2_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k5_relat_1(X1,X2))
        & v1_funct_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ( ( v2_funct_1(k5_relat_1(X2,X1))
                & r1_tarski(k2_relat_1(X2),k1_relat_1(X1)) )
             => v2_funct_1(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t47_funct_1])).

fof(c_0_7,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X16)
      | ~ v1_relat_1(X17)
      | ~ r1_tarski(k2_relat_1(X16),k1_relat_1(X17))
      | k1_relat_1(k5_relat_1(X16,X17)) = k1_relat_1(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_relat_1])])])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & v2_funct_1(k5_relat_1(esk4_0,esk3_0))
    & r1_tarski(k2_relat_1(esk4_0),k1_relat_1(esk3_0))
    & ~ v2_funct_1(esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v2_funct_1(X4)
        | ~ r2_hidden(X5,k1_relat_1(X4))
        | ~ r2_hidden(X6,k1_relat_1(X4))
        | k1_funct_1(X4,X5) != k1_funct_1(X4,X6)
        | X5 = X6
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X4) )
      & ( r2_hidden(esk1_1(X4),k1_relat_1(X4))
        | v2_funct_1(X4)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X4) )
      & ( r2_hidden(esk2_1(X4),k1_relat_1(X4))
        | v2_funct_1(X4)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X4) )
      & ( k1_funct_1(X4,esk1_1(X4)) = k1_funct_1(X4,esk2_1(X4))
        | v2_funct_1(X4)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X4) )
      & ( esk1_1(X4) != esk2_1(X4)
        | v2_funct_1(X4)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

cnf(c_0_10,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),k1_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( X2 = X3
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk4_0,esk3_0)) = k1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13])])).

cnf(c_0_16,negated_conjecture,
    ( v2_funct_1(k5_relat_1(esk4_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_17,plain,(
    ! [X13,X14,X15] :
      ( ~ v1_relat_1(X14)
      | ~ v1_funct_1(X14)
      | ~ v1_relat_1(X15)
      | ~ v1_funct_1(X15)
      | ~ r2_hidden(X13,k1_relat_1(X14))
      | k1_funct_1(k5_relat_1(X14,X15),X13) = k1_funct_1(X15,k1_funct_1(X14,X13)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).

cnf(c_0_18,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(k5_relat_1(esk4_0,esk3_0),X1) != k1_funct_1(k5_relat_1(esk4_0,esk3_0),X2)
    | ~ r2_hidden(X2,k1_relat_1(esk4_0))
    | ~ r2_hidden(X1,k1_relat_1(esk4_0))
    | ~ v1_funct_1(k5_relat_1(esk4_0,esk3_0))
    | ~ v1_relat_1(k5_relat_1(esk4_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

cnf(c_0_19,plain,
    ( k1_funct_1(k5_relat_1(X1,X2),X3) = k1_funct_1(X2,k1_funct_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_22,plain,(
    ! [X11,X12] :
      ( ( v1_relat_1(k5_relat_1(X11,X12))
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( v1_funct_1(k5_relat_1(X11,X12))
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).

cnf(c_0_23,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(k5_relat_1(esk4_0,esk3_0),X1) != k1_funct_1(esk3_0,k1_funct_1(esk4_0,X2))
    | ~ r2_hidden(X2,k1_relat_1(esk4_0))
    | ~ r2_hidden(X1,k1_relat_1(esk4_0))
    | ~ v1_funct_1(k5_relat_1(esk4_0,esk3_0))
    | ~ v1_relat_1(k5_relat_1(esk4_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_12]),c_0_13])])).

cnf(c_0_24,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_25,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X9)
      | ~ v1_relat_1(X10)
      | v1_relat_1(k5_relat_1(X9,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_26,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(k5_relat_1(esk4_0,esk3_0),X1) != k1_funct_1(esk3_0,k1_funct_1(esk4_0,X2))
    | ~ r2_hidden(X2,k1_relat_1(esk4_0))
    | ~ r2_hidden(X1,k1_relat_1(esk4_0))
    | ~ v1_relat_1(k5_relat_1(esk4_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_20]),c_0_21]),c_0_12]),c_0_13])])).

cnf(c_0_27,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_28,plain,
    ( r2_hidden(esk2_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,plain,
    ( k1_funct_1(X1,esk1_1(X1)) = k1_funct_1(X1,esk2_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(k5_relat_1(esk4_0,esk3_0),X1) != k1_funct_1(esk3_0,k1_funct_1(esk4_0,X2))
    | ~ r2_hidden(X2,k1_relat_1(esk4_0))
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_12]),c_0_13])])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),k1_relat_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_21]),c_0_13])]),c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( k1_funct_1(esk4_0,esk2_1(esk4_0)) = k1_funct_1(esk4_0,esk1_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_21]),c_0_13])]),c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( X1 = esk2_1(esk4_0)
    | k1_funct_1(k5_relat_1(esk4_0,esk3_0),X1) != k1_funct_1(esk3_0,k1_funct_1(esk4_0,esk1_1(esk4_0)))
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_35,plain,
    ( r2_hidden(esk1_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_36,negated_conjecture,
    ( X1 = esk2_1(esk4_0)
    | k1_funct_1(esk3_0,k1_funct_1(esk4_0,X1)) != k1_funct_1(esk3_0,k1_funct_1(esk4_0,esk1_1(esk4_0)))
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_19]),c_0_20]),c_0_21]),c_0_12]),c_0_13])])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk1_1(esk4_0),k1_relat_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_21]),c_0_13])]),c_0_29])).

cnf(c_0_38,plain,
    ( v2_funct_1(X1)
    | esk1_1(X1) != esk2_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_39,negated_conjecture,
    ( esk2_1(esk4_0) = esk1_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_21]),c_0_13])]),c_0_29]),
    [proof]).

%------------------------------------------------------------------------------
