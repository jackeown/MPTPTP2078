%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0639+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:57 EST 2020

% Result     : Theorem 0.08s
% Output     : CNFRefutation 0.08s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 141 expanded)
%              Number of clauses        :   34 (  56 expanded)
%              Number of leaves         :    6 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  291 (1028 expanded)
%              Number of equality atoms :   32 (  91 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal clause size      :   23 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

fof(t22_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
           => k1_funct_1(k5_relat_1(X3,X2),X1) = k1_funct_1(X2,k1_funct_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(fc2_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k5_relat_1(X1,X2))
        & v1_funct_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(t46_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X2) )
           => v2_funct_1(k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_funct_1)).

fof(c_0_6,plain,(
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

fof(c_0_7,plain,(
    ! [X13,X14,X15] :
      ( ( r2_hidden(X13,k1_relat_1(X15))
        | ~ r2_hidden(X13,k1_relat_1(k5_relat_1(X15,X14)))
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( r2_hidden(k1_funct_1(X15,X13),k1_relat_1(X14))
        | ~ r2_hidden(X13,k1_relat_1(k5_relat_1(X15,X14)))
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( ~ r2_hidden(X13,k1_relat_1(X15))
        | ~ r2_hidden(k1_funct_1(X15,X13),k1_relat_1(X14))
        | r2_hidden(X13,k1_relat_1(k5_relat_1(X15,X14)))
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_funct_1])])])])).

fof(c_0_8,plain,(
    ! [X16,X17,X18] :
      ( ~ v1_relat_1(X17)
      | ~ v1_funct_1(X17)
      | ~ v1_relat_1(X18)
      | ~ v1_funct_1(X18)
      | ~ r2_hidden(X16,k1_relat_1(k5_relat_1(X18,X17)))
      | k1_funct_1(k5_relat_1(X18,X17),X16) = k1_funct_1(X17,k1_funct_1(X18,X16)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).

fof(c_0_9,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X9)
      | ~ v1_relat_1(X10)
      | v1_relat_1(k5_relat_1(X9,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_10,plain,(
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

cnf(c_0_11,plain,
    ( X2 = X3
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k1_relat_1(X3))
    | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X1,X3)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k1_funct_1(k5_relat_1(X2,X1),X3) = k1_funct_1(X1,k1_funct_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( X1 = k1_funct_1(X2,X3)
    | k1_funct_1(X4,X1) != k1_funct_1(X4,k1_funct_1(X2,X3))
    | ~ r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X4)))
    | ~ r2_hidden(X1,k1_relat_1(X4))
    | ~ v2_funct_1(X4)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,plain,
    ( k1_funct_1(X1,esk1_1(X1)) = k1_funct_1(X1,esk2_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,plain,
    ( k1_funct_1(k5_relat_1(X1,X2),esk1_1(k5_relat_1(X1,X2))) = k1_funct_1(X2,k1_funct_1(X1,esk1_1(k5_relat_1(X1,X2))))
    | v2_funct_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])).

cnf(c_0_20,plain,
    ( X1 = k1_funct_1(X2,esk1_1(k5_relat_1(X2,X3)))
    | v2_funct_1(k5_relat_1(X2,X3))
    | k1_funct_1(X3,X1) != k1_funct_1(X3,k1_funct_1(X2,esk1_1(k5_relat_1(X2,X3))))
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_14]),c_0_15]),c_0_16])).

cnf(c_0_21,plain,
    ( k1_funct_1(X1,k1_funct_1(X2,esk1_1(k5_relat_1(X2,X1)))) = k1_funct_1(k5_relat_1(X2,X1),esk2_1(k5_relat_1(X2,X1)))
    | v2_funct_1(k5_relat_1(X2,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_15]),c_0_16])).

cnf(c_0_22,plain,
    ( r2_hidden(esk2_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,plain,
    ( X1 = k1_funct_1(X2,esk1_1(k5_relat_1(X2,X3)))
    | v2_funct_1(k5_relat_1(X2,X3))
    | k1_funct_1(X3,X1) != k1_funct_1(k5_relat_1(X2,X3),esk2_1(k5_relat_1(X2,X3)))
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,plain,
    ( k1_funct_1(k5_relat_1(X1,X2),esk2_1(k5_relat_1(X1,X2))) = k1_funct_1(X2,k1_funct_1(X1,esk2_1(k5_relat_1(X1,X2))))
    | v2_funct_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_22]),c_0_15]),c_0_16])).

cnf(c_0_25,plain,
    ( X1 = k1_funct_1(X2,esk1_1(k5_relat_1(X2,X3)))
    | v2_funct_1(k5_relat_1(X2,X3))
    | k1_funct_1(X3,X1) != k1_funct_1(X3,k1_funct_1(X2,esk2_1(k5_relat_1(X2,X3))))
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_27,plain,
    ( k1_funct_1(X1,esk1_1(k5_relat_1(X1,X2))) = k1_funct_1(X1,esk2_1(k5_relat_1(X1,X2)))
    | v2_funct_1(k5_relat_1(X1,X2))
    | ~ r2_hidden(k1_funct_1(X1,esk2_1(k5_relat_1(X1,X2))),k1_relat_1(X2))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_1(k5_relat_1(X1,X2)),k1_relat_1(X1))
    | v2_funct_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_14]),c_0_15]),c_0_16])).

cnf(c_0_29,plain,
    ( k1_funct_1(X1,esk1_1(k5_relat_1(X1,X2))) = k1_funct_1(X1,esk2_1(k5_relat_1(X1,X2)))
    | v2_funct_1(k5_relat_1(X1,X2))
    | ~ r2_hidden(esk2_1(k5_relat_1(X1,X2)),k1_relat_1(k5_relat_1(X1,X2)))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_12])).

cnf(c_0_30,plain,
    ( X1 = esk1_1(k5_relat_1(X2,X3))
    | v2_funct_1(k5_relat_1(X2,X3))
    | k1_funct_1(X2,X1) != k1_funct_1(X2,esk1_1(k5_relat_1(X2,X3)))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_11,c_0_28])).

cnf(c_0_31,plain,
    ( k1_funct_1(X1,esk1_1(k5_relat_1(X1,X2))) = k1_funct_1(X1,esk2_1(k5_relat_1(X1,X2)))
    | v2_funct_1(k5_relat_1(X1,X2))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_22]),c_0_15]),c_0_16])).

fof(c_0_32,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ( ( v2_funct_1(X1)
                & v2_funct_1(X2) )
             => v2_funct_1(k5_relat_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t46_funct_1])).

cnf(c_0_33,plain,
    ( X1 = esk1_1(k5_relat_1(X2,X3))
    | v2_funct_1(k5_relat_1(X2,X3))
    | k1_funct_1(X2,X1) != k1_funct_1(X2,esk2_1(k5_relat_1(X2,X3)))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v2_funct_1(X2)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,plain,
    ( r2_hidden(esk2_1(k5_relat_1(X1,X2)),k1_relat_1(X1))
    | v2_funct_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_22]),c_0_15]),c_0_16])).

fof(c_0_35,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & v2_funct_1(esk3_0)
    & v2_funct_1(esk4_0)
    & ~ v2_funct_1(k5_relat_1(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).

cnf(c_0_36,plain,
    ( v2_funct_1(X1)
    | esk1_1(X1) != esk2_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_37,plain,
    ( esk1_1(k5_relat_1(X1,X2)) = esk2_1(k5_relat_1(X1,X2))
    | v2_funct_1(k5_relat_1(X1,X2))
    | ~ v2_funct_1(X1)
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_33]),c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( ~ v2_funct_1(k5_relat_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,plain,
    ( v2_funct_1(k5_relat_1(X1,X2))
    | ~ v2_funct_1(X1)
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_15]),c_0_16])).

cnf(c_0_40,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45])]),
    [proof]).

%------------------------------------------------------------------------------
