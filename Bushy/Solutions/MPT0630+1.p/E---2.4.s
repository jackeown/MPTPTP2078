%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t27_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:22 EDT 2019

% Result     : Theorem 0.41s
% Output     : CNFRefutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   28 (  66 expanded)
%              Number of clauses        :   19 (  24 expanded)
%              Number of leaves         :    4 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :  141 ( 367 expanded)
%              Number of equality atoms :   21 (  60 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t27_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(X2)
           => r1_tarski(k2_relat_1(X2),k1_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t27_funct_1.p',t27_funct_1)).

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
    file('/export/starexec/sandbox/benchmark/funct_1__t27_funct_1.p',d5_funct_1)).

fof(t21_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
          <=> ( r2_hidden(X1,k1_relat_1(X3))
              & r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t27_funct_1.p',t21_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t27_funct_1.p',d3_tarski)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ( k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(X2)
             => r1_tarski(k2_relat_1(X2),k1_relat_1(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t27_funct_1])).

fof(c_0_5,plain,(
    ! [X15,X16,X17,X19,X20,X21,X23] :
      ( ( r2_hidden(esk4_3(X15,X16,X17),k1_relat_1(X15))
        | ~ r2_hidden(X17,X16)
        | X16 != k2_relat_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( X17 = k1_funct_1(X15,esk4_3(X15,X16,X17))
        | ~ r2_hidden(X17,X16)
        | X16 != k2_relat_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( ~ r2_hidden(X20,k1_relat_1(X15))
        | X19 != k1_funct_1(X15,X20)
        | r2_hidden(X19,X16)
        | X16 != k2_relat_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( ~ r2_hidden(esk5_2(X15,X21),X21)
        | ~ r2_hidden(X23,k1_relat_1(X15))
        | esk5_2(X15,X21) != k1_funct_1(X15,X23)
        | X21 = k2_relat_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( r2_hidden(esk6_2(X15,X21),k1_relat_1(X15))
        | r2_hidden(esk5_2(X15,X21),X21)
        | X21 = k2_relat_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( esk5_2(X15,X21) = k1_funct_1(X15,esk6_2(X15,X21))
        | r2_hidden(esk5_2(X15,X21),X21)
        | X21 = k2_relat_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_6,plain,(
    ! [X31,X32,X33] :
      ( ( r2_hidden(X31,k1_relat_1(X33))
        | ~ r2_hidden(X31,k1_relat_1(k5_relat_1(X33,X32)))
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( r2_hidden(k1_funct_1(X33,X31),k1_relat_1(X32))
        | ~ r2_hidden(X31,k1_relat_1(k5_relat_1(X33,X32)))
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( ~ r2_hidden(X31,k1_relat_1(X33))
        | ~ r2_hidden(k1_funct_1(X33,X31),k1_relat_1(X32))
        | r2_hidden(X31,k1_relat_1(k5_relat_1(X33,X32)))
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_funct_1])])])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & k1_relat_1(k5_relat_1(esk2_0,esk1_0)) = k1_relat_1(esk2_0)
    & ~ r1_tarski(k2_relat_1(esk2_0),k1_relat_1(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_8,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk3_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk3_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k1_relat_1(X3))
    | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X1,X3)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk2_0,esk1_0)) = k1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,plain,
    ( r2_hidden(esk4_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_17,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( X1 = k1_funct_1(X2,esk4_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk2_0,X1),k1_relat_1(esk1_0))
    | ~ r2_hidden(X1,k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_20,plain,
    ( r2_hidden(esk4_3(X1,k2_relat_1(X1),esk3_2(k2_relat_1(X1),X2)),k1_relat_1(X1))
    | r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( k1_funct_1(X1,esk4_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk2_0,esk4_3(esk2_0,k2_relat_1(esk2_0),esk3_2(k2_relat_1(esk2_0),X1))),k1_relat_1(esk1_0))
    | r1_tarski(k2_relat_1(esk2_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_13]),c_0_15])])).

cnf(c_0_23,plain,
    ( k1_funct_1(X1,esk4_3(X1,k2_relat_1(X1),esk3_2(k2_relat_1(X1),X2))) = esk3_2(k2_relat_1(X1),X2)
    | r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_17])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk3_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk3_2(k2_relat_1(esk2_0),X1),k1_relat_1(esk1_0))
    | r1_tarski(k2_relat_1(esk2_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_13]),c_0_15])])).

cnf(c_0_26,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk2_0),k1_relat_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),
    [proof]).
%------------------------------------------------------------------------------
