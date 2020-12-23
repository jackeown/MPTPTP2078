%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t40_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:23 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   30 ( 145 expanded)
%              Number of clauses        :   19 (  52 expanded)
%              Number of leaves         :    5 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :  126 ( 642 expanded)
%              Number of equality atoms :   15 (  45 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   19 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t40_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,k6_relat_1(X2))))
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(k1_funct_1(X3,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t40_funct_1.p',t40_funct_1)).

fof(t34_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( X2 = k6_relat_1(X1)
      <=> ( k1_relat_1(X2) = X1
          & ! [X3] :
              ( r2_hidden(X3,X1)
             => k1_funct_1(X2,X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t40_funct_1.p',t34_funct_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t40_funct_1.p',fc3_funct_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t40_funct_1.p',dt_k6_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/funct_1__t40_funct_1.p',t21_funct_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,k6_relat_1(X2))))
        <=> ( r2_hidden(X1,k1_relat_1(X3))
            & r2_hidden(k1_funct_1(X3,X1),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t40_funct_1])).

fof(c_0_6,plain,(
    ! [X21,X22,X23] :
      ( ( k1_relat_1(X22) = X21
        | X22 != k6_relat_1(X21)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( ~ r2_hidden(X23,X21)
        | k1_funct_1(X22,X23) = X23
        | X22 != k6_relat_1(X21)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( r2_hidden(esk5_2(X21,X22),X21)
        | k1_relat_1(X22) != X21
        | X22 = k6_relat_1(X21)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( k1_funct_1(X22,esk5_2(X21,X22)) != esk5_2(X21,X22)
        | k1_relat_1(X22) != X21
        | X22 = k6_relat_1(X21)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).

fof(c_0_7,plain,(
    ! [X30] :
      ( v1_relat_1(k6_relat_1(X30))
      & v1_funct_1(k6_relat_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_8,plain,(
    ! [X11] : v1_relat_1(k6_relat_1(X11)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_9,plain,(
    ! [X16,X17,X18] :
      ( ( r2_hidden(X16,k1_relat_1(X18))
        | ~ r2_hidden(X16,k1_relat_1(k5_relat_1(X18,X17)))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( r2_hidden(k1_funct_1(X18,X16),k1_relat_1(X17))
        | ~ r2_hidden(X16,k1_relat_1(k5_relat_1(X18,X17)))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( ~ r2_hidden(X16,k1_relat_1(X18))
        | ~ r2_hidden(k1_funct_1(X18,X16),k1_relat_1(X17))
        | r2_hidden(X16,k1_relat_1(k5_relat_1(X18,X17)))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_funct_1])])])])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & ( ~ r2_hidden(esk1_0,k1_relat_1(k5_relat_1(esk3_0,k6_relat_1(esk2_0))))
      | ~ r2_hidden(esk1_0,k1_relat_1(esk3_0))
      | ~ r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0) )
    & ( r2_hidden(esk1_0,k1_relat_1(esk3_0))
      | r2_hidden(esk1_0,k1_relat_1(k5_relat_1(esk3_0,k6_relat_1(esk2_0)))) )
    & ( r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0)
      | r2_hidden(esk1_0,k1_relat_1(k5_relat_1(esk3_0,k6_relat_1(esk2_0)))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

cnf(c_0_11,plain,
    ( k1_relat_1(X1) = X2
    | X1 != k6_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(esk3_0))
    | r2_hidden(esk1_0,k1_relat_1(k5_relat_1(esk3_0,k6_relat_1(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k1_relat_1(X3))
    | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X1,X3)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_12]),c_0_13])])).

cnf(c_0_20,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k1_relat_1(k5_relat_1(esk3_0,k6_relat_1(esk2_0))))
    | ~ r2_hidden(esk1_0,k1_relat_1(esk3_0))
    | ~ r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_12]),c_0_16]),c_0_13]),c_0_17])])).

cnf(c_0_22,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X1,k6_relat_1(X3))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_12]),c_0_13])])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0)
    | r2_hidden(esk1_0,k1_relat_1(k5_relat_1(esk3_0,k6_relat_1(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k1_relat_1(k5_relat_1(esk3_0,k6_relat_1(esk2_0))))
    | ~ r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_16]),c_0_17])])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X3))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k1_relat_1(k5_relat_1(esk3_0,k6_relat_1(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25])])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k1_relat_1(k5_relat_1(X2,k6_relat_1(X3))))
    | ~ r2_hidden(k1_funct_1(X2,X1),X3)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_19]),c_0_12]),c_0_13])])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_25]),c_0_21]),c_0_16]),c_0_17])]),
    [proof]).
%------------------------------------------------------------------------------
