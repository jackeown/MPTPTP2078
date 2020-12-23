%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t57_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:25 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   27 (  87 expanded)
%              Number of clauses        :   16 (  28 expanded)
%              Number of leaves         :    5 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  245 ( 543 expanded)
%              Number of equality atoms :   69 ( 153 expanded)
%              Maximal formula depth    :   31 (   6 average)
%              Maximal clause size      :  130 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t57_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & r2_hidden(X1,k2_relat_1(X2)) )
       => ( X1 = k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))
          & X1 = k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t57_funct_1.p',t57_funct_1)).

fof(t23_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(X2))
           => k1_funct_1(k5_relat_1(X2,X3),X1) = k1_funct_1(X3,k1_funct_1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t57_funct_1.p',t23_funct_1)).

fof(t54_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ( X2 = k2_funct_1(X1)
            <=> ( k1_relat_1(X2) = k2_relat_1(X1)
                & ! [X3,X4] :
                    ( ( ( r2_hidden(X3,k2_relat_1(X1))
                        & X4 = k1_funct_1(X2,X3) )
                     => ( r2_hidden(X4,k1_relat_1(X1))
                        & X3 = k1_funct_1(X1,X4) ) )
                    & ( ( r2_hidden(X4,k1_relat_1(X1))
                        & X3 = k1_funct_1(X1,X4) )
                     => ( r2_hidden(X3,k2_relat_1(X1))
                        & X4 = k1_funct_1(X2,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t57_funct_1.p',t54_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t57_funct_1.p',dt_k2_funct_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t57_funct_1.p',t55_funct_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( ( v2_funct_1(X2)
            & r2_hidden(X1,k2_relat_1(X2)) )
         => ( X1 = k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))
            & X1 = k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t57_funct_1])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & v2_funct_1(esk2_0)
    & r2_hidden(esk1_0,k2_relat_1(esk2_0))
    & ( esk1_0 != k1_funct_1(esk2_0,k1_funct_1(k2_funct_1(esk2_0),esk1_0))
      | esk1_0 != k1_funct_1(k5_relat_1(k2_funct_1(esk2_0),esk2_0),esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_7,plain,(
    ! [X16,X17,X18] :
      ( ~ v1_relat_1(X17)
      | ~ v1_funct_1(X17)
      | ~ v1_relat_1(X18)
      | ~ v1_funct_1(X18)
      | ~ r2_hidden(X16,k1_relat_1(X17))
      | k1_funct_1(k5_relat_1(X17,X18),X16) = k1_funct_1(X18,k1_funct_1(X17,X16)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).

fof(c_0_8,plain,(
    ! [X21,X22,X23,X24,X25,X26] :
      ( ( k1_relat_1(X22) = k2_relat_1(X21)
        | X22 != k2_funct_1(X21)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v2_funct_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( r2_hidden(X24,k1_relat_1(X21))
        | ~ r2_hidden(X23,k2_relat_1(X21))
        | X24 != k1_funct_1(X22,X23)
        | X22 != k2_funct_1(X21)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v2_funct_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( X23 = k1_funct_1(X21,X24)
        | ~ r2_hidden(X23,k2_relat_1(X21))
        | X24 != k1_funct_1(X22,X23)
        | X22 != k2_funct_1(X21)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v2_funct_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( r2_hidden(X25,k2_relat_1(X21))
        | ~ r2_hidden(X26,k1_relat_1(X21))
        | X25 != k1_funct_1(X21,X26)
        | X22 != k2_funct_1(X21)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v2_funct_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( X26 = k1_funct_1(X22,X25)
        | ~ r2_hidden(X26,k1_relat_1(X21))
        | X25 != k1_funct_1(X21,X26)
        | X22 != k2_funct_1(X21)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v2_funct_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( r2_hidden(esk7_2(X21,X22),k1_relat_1(X21))
        | r2_hidden(esk4_2(X21,X22),k2_relat_1(X21))
        | k1_relat_1(X22) != k2_relat_1(X21)
        | X22 = k2_funct_1(X21)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v2_funct_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( esk6_2(X21,X22) = k1_funct_1(X21,esk7_2(X21,X22))
        | r2_hidden(esk4_2(X21,X22),k2_relat_1(X21))
        | k1_relat_1(X22) != k2_relat_1(X21)
        | X22 = k2_funct_1(X21)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v2_funct_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( ~ r2_hidden(esk6_2(X21,X22),k2_relat_1(X21))
        | esk7_2(X21,X22) != k1_funct_1(X22,esk6_2(X21,X22))
        | r2_hidden(esk4_2(X21,X22),k2_relat_1(X21))
        | k1_relat_1(X22) != k2_relat_1(X21)
        | X22 = k2_funct_1(X21)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v2_funct_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( r2_hidden(esk7_2(X21,X22),k1_relat_1(X21))
        | esk5_2(X21,X22) = k1_funct_1(X22,esk4_2(X21,X22))
        | k1_relat_1(X22) != k2_relat_1(X21)
        | X22 = k2_funct_1(X21)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v2_funct_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( esk6_2(X21,X22) = k1_funct_1(X21,esk7_2(X21,X22))
        | esk5_2(X21,X22) = k1_funct_1(X22,esk4_2(X21,X22))
        | k1_relat_1(X22) != k2_relat_1(X21)
        | X22 = k2_funct_1(X21)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v2_funct_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( ~ r2_hidden(esk6_2(X21,X22),k2_relat_1(X21))
        | esk7_2(X21,X22) != k1_funct_1(X22,esk6_2(X21,X22))
        | esk5_2(X21,X22) = k1_funct_1(X22,esk4_2(X21,X22))
        | k1_relat_1(X22) != k2_relat_1(X21)
        | X22 = k2_funct_1(X21)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v2_funct_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( r2_hidden(esk7_2(X21,X22),k1_relat_1(X21))
        | ~ r2_hidden(esk5_2(X21,X22),k1_relat_1(X21))
        | esk4_2(X21,X22) != k1_funct_1(X21,esk5_2(X21,X22))
        | k1_relat_1(X22) != k2_relat_1(X21)
        | X22 = k2_funct_1(X21)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v2_funct_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( esk6_2(X21,X22) = k1_funct_1(X21,esk7_2(X21,X22))
        | ~ r2_hidden(esk5_2(X21,X22),k1_relat_1(X21))
        | esk4_2(X21,X22) != k1_funct_1(X21,esk5_2(X21,X22))
        | k1_relat_1(X22) != k2_relat_1(X21)
        | X22 = k2_funct_1(X21)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v2_funct_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( ~ r2_hidden(esk6_2(X21,X22),k2_relat_1(X21))
        | esk7_2(X21,X22) != k1_funct_1(X22,esk6_2(X21,X22))
        | ~ r2_hidden(esk5_2(X21,X22),k1_relat_1(X21))
        | esk4_2(X21,X22) != k1_funct_1(X21,esk5_2(X21,X22))
        | k1_relat_1(X22) != k2_relat_1(X21)
        | X22 = k2_funct_1(X21)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v2_funct_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_funct_1])])])])])])).

fof(c_0_9,plain,(
    ! [X9] :
      ( ( v1_relat_1(k2_funct_1(X9))
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( v1_funct_1(k2_funct_1(X9))
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_10,negated_conjecture,
    ( esk1_0 != k1_funct_1(esk2_0,k1_funct_1(k2_funct_1(esk2_0),esk1_0))
    | esk1_0 != k1_funct_1(k5_relat_1(k2_funct_1(esk2_0),esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k1_funct_1(k5_relat_1(X1,X2),X3) = k1_funct_1(X2,k1_funct_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | X3 != k1_funct_1(X4,X1)
    | X4 != k2_funct_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_funct_1(X4)
    | ~ v2_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( k1_funct_1(esk2_0,k1_funct_1(k2_funct_1(esk2_0),esk1_0)) != esk1_0
    | ~ r2_hidden(esk1_0,k1_relat_1(k2_funct_1(esk2_0)))
    | ~ v1_funct_1(k2_funct_1(esk2_0))
    | ~ v1_relat_1(k2_funct_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13])])).

cnf(c_0_18,plain,
    ( k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X2)) = X2
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_14])]),c_0_15]),c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk1_0,k2_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,negated_conjecture,
    ( v2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_21,plain,(
    ! [X31] :
      ( ( k2_relat_1(X31) = k1_relat_1(k2_funct_1(X31))
        | ~ v2_funct_1(X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( k1_relat_1(X31) = k2_relat_1(k2_funct_1(X31))
        | ~ v2_funct_1(X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k1_relat_1(k2_funct_1(esk2_0)))
    | ~ v1_funct_1(k2_funct_1(esk2_0))
    | ~ v1_relat_1(k2_funct_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_12]),c_0_13])])).

cnf(c_0_23,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk2_0))
    | ~ v1_relat_1(k2_funct_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_19]),c_0_20]),c_0_12]),c_0_13])])).

cnf(c_0_25,negated_conjecture,
    ( ~ v1_relat_1(k2_funct_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_16]),c_0_12]),c_0_13])])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_15]),c_0_12]),c_0_13])]),
    [proof]).
%------------------------------------------------------------------------------
