%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t47_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:24 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 176 expanded)
%              Number of clauses        :   28 (  56 expanded)
%              Number of leaves         :    6 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  180 (1062 expanded)
%              Number of equality atoms :   34 (  73 expanded)
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
    file('/export/starexec/sandbox2/benchmark/funct_1__t47_funct_1.p',t47_funct_1)).

fof(t46_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
           => k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t47_funct_1.p',t46_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/funct_1__t47_funct_1.p',d8_funct_1)).

fof(fc2_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k5_relat_1(X1,X2))
        & v1_funct_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t47_funct_1.p',fc2_funct_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t47_funct_1.p',dt_k5_relat_1)).

fof(t23_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(X2))
           => k1_funct_1(k5_relat_1(X2,X3),X1) = k1_funct_1(X3,k1_funct_1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t47_funct_1.p',t23_funct_1)).

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
    ! [X26,X27] :
      ( ~ v1_relat_1(X26)
      | ~ v1_relat_1(X27)
      | ~ r1_tarski(k2_relat_1(X26),k1_relat_1(X27))
      | k1_relat_1(k5_relat_1(X26,X27)) = k1_relat_1(X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_relat_1])])])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & v2_funct_1(k5_relat_1(esk2_0,esk1_0))
    & r1_tarski(k2_relat_1(esk2_0),k1_relat_1(esk1_0))
    & ~ v2_funct_1(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v2_funct_1(X8)
        | ~ r2_hidden(X9,k1_relat_1(X8))
        | ~ r2_hidden(X10,k1_relat_1(X8))
        | k1_funct_1(X8,X9) != k1_funct_1(X8,X10)
        | X9 = X10
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( r2_hidden(esk3_1(X8),k1_relat_1(X8))
        | v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( r2_hidden(esk4_1(X8),k1_relat_1(X8))
        | v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( k1_funct_1(X8,esk3_1(X8)) = k1_funct_1(X8,esk4_1(X8))
        | v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( esk3_1(X8) != esk4_1(X8)
        | v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

cnf(c_0_10,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk2_0),k1_relat_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
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
    ( k1_relat_1(k5_relat_1(esk2_0,esk1_0)) = k1_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13])])).

cnf(c_0_16,negated_conjecture,
    ( v2_funct_1(k5_relat_1(esk2_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_17,plain,(
    ! [X39,X40] :
      ( ( v1_relat_1(k5_relat_1(X39,X40))
        | ~ v1_relat_1(X39)
        | ~ v1_funct_1(X39)
        | ~ v1_relat_1(X40)
        | ~ v1_funct_1(X40) )
      & ( v1_funct_1(k5_relat_1(X39,X40))
        | ~ v1_relat_1(X39)
        | ~ v1_funct_1(X39)
        | ~ v1_relat_1(X40)
        | ~ v1_funct_1(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).

cnf(c_0_18,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(k5_relat_1(esk2_0,esk1_0),X1) != k1_funct_1(k5_relat_1(esk2_0,esk1_0),X2)
    | ~ r2_hidden(X2,k1_relat_1(esk2_0))
    | ~ r2_hidden(X1,k1_relat_1(esk2_0))
    | ~ v1_funct_1(k5_relat_1(esk2_0,esk1_0))
    | ~ v1_relat_1(k5_relat_1(esk2_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

cnf(c_0_19,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_22,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ v1_relat_1(X14)
      | v1_relat_1(k5_relat_1(X13,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_23,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(k5_relat_1(esk2_0,esk1_0),X1) != k1_funct_1(k5_relat_1(esk2_0,esk1_0),X2)
    | ~ r2_hidden(X2,k1_relat_1(esk2_0))
    | ~ r2_hidden(X1,k1_relat_1(esk2_0))
    | ~ v1_relat_1(k5_relat_1(esk2_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_12]),c_0_13])])).

cnf(c_0_24,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(k5_relat_1(esk2_0,esk1_0),X1) != k1_funct_1(k5_relat_1(esk2_0,esk1_0),X2)
    | ~ r2_hidden(X2,k1_relat_1(esk2_0))
    | ~ r2_hidden(X1,k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_12]),c_0_13])])).

cnf(c_0_26,plain,
    ( r2_hidden(esk4_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_28,plain,(
    ! [X19,X20,X21] :
      ( ~ v1_relat_1(X20)
      | ~ v1_funct_1(X20)
      | ~ v1_relat_1(X21)
      | ~ v1_funct_1(X21)
      | ~ r2_hidden(X19,k1_relat_1(X20))
      | k1_funct_1(k5_relat_1(X20,X21),X19) = k1_funct_1(X21,k1_funct_1(X20,X19)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).

cnf(c_0_29,negated_conjecture,
    ( X1 = esk4_1(esk2_0)
    | k1_funct_1(k5_relat_1(esk2_0,esk1_0),X1) != k1_funct_1(k5_relat_1(esk2_0,esk1_0),esk4_1(esk2_0))
    | ~ r2_hidden(X1,k1_relat_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_21]),c_0_13])]),c_0_27])).

cnf(c_0_30,plain,
    ( r2_hidden(esk3_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,plain,
    ( k1_funct_1(k5_relat_1(X1,X2),X3) = k1_funct_1(X2,k1_funct_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( esk4_1(esk2_0) = esk3_1(esk2_0)
    | k1_funct_1(k5_relat_1(esk2_0,esk1_0),esk4_1(esk2_0)) != k1_funct_1(k5_relat_1(esk2_0,esk1_0),esk3_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_21]),c_0_13])]),c_0_27])).

cnf(c_0_33,plain,
    ( k1_funct_1(k5_relat_1(X1,X2),esk4_1(X1)) = k1_funct_1(X2,k1_funct_1(X1,esk4_1(X1)))
    | v2_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( esk4_1(esk2_0) = esk3_1(esk2_0)
    | k1_funct_1(k5_relat_1(esk2_0,esk1_0),esk3_1(esk2_0)) != k1_funct_1(esk1_0,k1_funct_1(esk2_0,esk4_1(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_20]),c_0_21]),c_0_12]),c_0_13])]),c_0_27])).

cnf(c_0_35,plain,
    ( k1_funct_1(k5_relat_1(X1,X2),esk3_1(X1)) = k1_funct_1(X2,k1_funct_1(X1,esk3_1(X1)))
    | v2_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( esk4_1(esk2_0) = esk3_1(esk2_0)
    | k1_funct_1(esk1_0,k1_funct_1(esk2_0,esk4_1(esk2_0))) != k1_funct_1(esk1_0,k1_funct_1(esk2_0,esk3_1(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_20]),c_0_21]),c_0_12]),c_0_13])]),c_0_27])).

cnf(c_0_37,plain,
    ( k1_funct_1(X1,esk3_1(X1)) = k1_funct_1(X1,esk4_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_38,plain,
    ( v2_funct_1(X1)
    | esk3_1(X1) != esk4_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_39,negated_conjecture,
    ( esk4_1(esk2_0) = esk3_1(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_21]),c_0_13])]),c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_21]),c_0_13])]),c_0_27]),
    [proof]).
%------------------------------------------------------------------------------
