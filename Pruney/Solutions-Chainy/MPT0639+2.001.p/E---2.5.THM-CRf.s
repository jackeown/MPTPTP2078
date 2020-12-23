%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:39 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
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
    ! [X6,X7,X8] :
      ( ( ~ v2_funct_1(X6)
        | ~ r2_hidden(X7,k1_relat_1(X6))
        | ~ r2_hidden(X8,k1_relat_1(X6))
        | k1_funct_1(X6,X7) != k1_funct_1(X6,X8)
        | X7 = X8
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(esk1_1(X6),k1_relat_1(X6))
        | v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(esk2_1(X6),k1_relat_1(X6))
        | v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( k1_funct_1(X6,esk1_1(X6)) = k1_funct_1(X6,esk2_1(X6))
        | v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( esk1_1(X6) != esk2_1(X6)
        | v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) ) ) ),
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
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | ~ v1_relat_1(X5)
      | v1_relat_1(k5_relat_1(X4,X5)) ) ),
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
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:45:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_AE_CS_SP_PI_S0Y
% 0.19/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.026 s
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(d8_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)<=>![X2, X3]:(((r2_hidden(X2,k1_relat_1(X1))&r2_hidden(X3,k1_relat_1(X1)))&k1_funct_1(X1,X2)=k1_funct_1(X1,X3))=>X2=X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 0.19/0.38  fof(t21_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_1)).
% 0.19/0.38  fof(t22_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))=>k1_funct_1(k5_relat_1(X3,X2),X1)=k1_funct_1(X2,k1_funct_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 0.19/0.38  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.19/0.38  fof(fc2_funct_1, axiom, ![X1, X2]:((((v1_relat_1(X1)&v1_funct_1(X1))&v1_relat_1(X2))&v1_funct_1(X2))=>(v1_relat_1(k5_relat_1(X1,X2))&v1_funct_1(k5_relat_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funct_1)).
% 0.19/0.38  fof(t46_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X1)&v2_funct_1(X2))=>v2_funct_1(k5_relat_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_funct_1)).
% 0.19/0.38  fof(c_0_6, plain, ![X6, X7, X8]:((~v2_funct_1(X6)|(~r2_hidden(X7,k1_relat_1(X6))|~r2_hidden(X8,k1_relat_1(X6))|k1_funct_1(X6,X7)!=k1_funct_1(X6,X8)|X7=X8)|(~v1_relat_1(X6)|~v1_funct_1(X6)))&((((r2_hidden(esk1_1(X6),k1_relat_1(X6))|v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6)))&(r2_hidden(esk2_1(X6),k1_relat_1(X6))|v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6))))&(k1_funct_1(X6,esk1_1(X6))=k1_funct_1(X6,esk2_1(X6))|v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6))))&(esk1_1(X6)!=esk2_1(X6)|v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).
% 0.19/0.38  fof(c_0_7, plain, ![X13, X14, X15]:(((r2_hidden(X13,k1_relat_1(X15))|~r2_hidden(X13,k1_relat_1(k5_relat_1(X15,X14)))|(~v1_relat_1(X15)|~v1_funct_1(X15))|(~v1_relat_1(X14)|~v1_funct_1(X14)))&(r2_hidden(k1_funct_1(X15,X13),k1_relat_1(X14))|~r2_hidden(X13,k1_relat_1(k5_relat_1(X15,X14)))|(~v1_relat_1(X15)|~v1_funct_1(X15))|(~v1_relat_1(X14)|~v1_funct_1(X14))))&(~r2_hidden(X13,k1_relat_1(X15))|~r2_hidden(k1_funct_1(X15,X13),k1_relat_1(X14))|r2_hidden(X13,k1_relat_1(k5_relat_1(X15,X14)))|(~v1_relat_1(X15)|~v1_funct_1(X15))|(~v1_relat_1(X14)|~v1_funct_1(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_funct_1])])])])).
% 0.19/0.38  fof(c_0_8, plain, ![X16, X17, X18]:(~v1_relat_1(X17)|~v1_funct_1(X17)|(~v1_relat_1(X18)|~v1_funct_1(X18)|(~r2_hidden(X16,k1_relat_1(k5_relat_1(X18,X17)))|k1_funct_1(k5_relat_1(X18,X17),X16)=k1_funct_1(X17,k1_funct_1(X18,X16))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).
% 0.19/0.38  fof(c_0_9, plain, ![X4, X5]:(~v1_relat_1(X4)|~v1_relat_1(X5)|v1_relat_1(k5_relat_1(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.19/0.38  fof(c_0_10, plain, ![X11, X12]:((v1_relat_1(k5_relat_1(X11,X12))|(~v1_relat_1(X11)|~v1_funct_1(X11)|~v1_relat_1(X12)|~v1_funct_1(X12)))&(v1_funct_1(k5_relat_1(X11,X12))|(~v1_relat_1(X11)|~v1_funct_1(X11)|~v1_relat_1(X12)|~v1_funct_1(X12)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).
% 0.19/0.38  cnf(c_0_11, plain, (X2=X3|~v2_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r2_hidden(X3,k1_relat_1(X1))|k1_funct_1(X1,X2)!=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_12, plain, (r2_hidden(k1_funct_1(X1,X2),k1_relat_1(X3))|~r2_hidden(X2,k1_relat_1(k5_relat_1(X1,X3)))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X3)|~v1_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.38  cnf(c_0_13, plain, (k1_funct_1(k5_relat_1(X2,X1),X3)=k1_funct_1(X1,k1_funct_1(X2,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.38  cnf(c_0_14, plain, (r2_hidden(esk1_1(X1),k1_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_15, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_16, plain, (v1_funct_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_17, plain, (X1=k1_funct_1(X2,X3)|k1_funct_1(X4,X1)!=k1_funct_1(X4,k1_funct_1(X2,X3))|~r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X4)))|~r2_hidden(X1,k1_relat_1(X4))|~v2_funct_1(X4)|~v1_funct_1(X4)|~v1_funct_1(X2)|~v1_relat_1(X4)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.19/0.38  cnf(c_0_18, plain, (k1_funct_1(X1,esk1_1(X1))=k1_funct_1(X1,esk2_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_19, plain, (k1_funct_1(k5_relat_1(X1,X2),esk1_1(k5_relat_1(X1,X2)))=k1_funct_1(X2,k1_funct_1(X1,esk1_1(k5_relat_1(X1,X2))))|v2_funct_1(k5_relat_1(X1,X2))|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16])).
% 0.19/0.38  cnf(c_0_20, plain, (X1=k1_funct_1(X2,esk1_1(k5_relat_1(X2,X3)))|v2_funct_1(k5_relat_1(X2,X3))|k1_funct_1(X3,X1)!=k1_funct_1(X3,k1_funct_1(X2,esk1_1(k5_relat_1(X2,X3))))|~r2_hidden(X1,k1_relat_1(X3))|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_1(X2)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_14]), c_0_15]), c_0_16])).
% 0.19/0.38  cnf(c_0_21, plain, (k1_funct_1(X1,k1_funct_1(X2,esk1_1(k5_relat_1(X2,X1))))=k1_funct_1(k5_relat_1(X2,X1),esk2_1(k5_relat_1(X2,X1)))|v2_funct_1(k5_relat_1(X2,X1))|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_15]), c_0_16])).
% 0.19/0.38  cnf(c_0_22, plain, (r2_hidden(esk2_1(X1),k1_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_23, plain, (X1=k1_funct_1(X2,esk1_1(k5_relat_1(X2,X3)))|v2_funct_1(k5_relat_1(X2,X3))|k1_funct_1(X3,X1)!=k1_funct_1(k5_relat_1(X2,X3),esk2_1(k5_relat_1(X2,X3)))|~r2_hidden(X1,k1_relat_1(X3))|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_1(X2)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.38  cnf(c_0_24, plain, (k1_funct_1(k5_relat_1(X1,X2),esk2_1(k5_relat_1(X1,X2)))=k1_funct_1(X2,k1_funct_1(X1,esk2_1(k5_relat_1(X1,X2))))|v2_funct_1(k5_relat_1(X1,X2))|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_22]), c_0_15]), c_0_16])).
% 0.19/0.38  cnf(c_0_25, plain, (X1=k1_funct_1(X2,esk1_1(k5_relat_1(X2,X3)))|v2_funct_1(k5_relat_1(X2,X3))|k1_funct_1(X3,X1)!=k1_funct_1(X3,k1_funct_1(X2,esk2_1(k5_relat_1(X2,X3))))|~r2_hidden(X1,k1_relat_1(X3))|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_1(X2)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.38  cnf(c_0_26, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X3)|~v1_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.38  cnf(c_0_27, plain, (k1_funct_1(X1,esk1_1(k5_relat_1(X1,X2)))=k1_funct_1(X1,esk2_1(k5_relat_1(X1,X2)))|v2_funct_1(k5_relat_1(X1,X2))|~r2_hidden(k1_funct_1(X1,esk2_1(k5_relat_1(X1,X2))),k1_relat_1(X2))|~v2_funct_1(X2)|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_25])).
% 0.19/0.38  cnf(c_0_28, plain, (r2_hidden(esk1_1(k5_relat_1(X1,X2)),k1_relat_1(X1))|v2_funct_1(k5_relat_1(X1,X2))|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_14]), c_0_15]), c_0_16])).
% 0.19/0.38  cnf(c_0_29, plain, (k1_funct_1(X1,esk1_1(k5_relat_1(X1,X2)))=k1_funct_1(X1,esk2_1(k5_relat_1(X1,X2)))|v2_funct_1(k5_relat_1(X1,X2))|~r2_hidden(esk2_1(k5_relat_1(X1,X2)),k1_relat_1(k5_relat_1(X1,X2)))|~v2_funct_1(X2)|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_27, c_0_12])).
% 0.19/0.38  cnf(c_0_30, plain, (X1=esk1_1(k5_relat_1(X2,X3))|v2_funct_1(k5_relat_1(X2,X3))|k1_funct_1(X2,X1)!=k1_funct_1(X2,esk1_1(k5_relat_1(X2,X3)))|~r2_hidden(X1,k1_relat_1(X2))|~v2_funct_1(X2)|~v1_funct_1(X2)|~v1_funct_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_11, c_0_28])).
% 0.19/0.38  cnf(c_0_31, plain, (k1_funct_1(X1,esk1_1(k5_relat_1(X1,X2)))=k1_funct_1(X1,esk2_1(k5_relat_1(X1,X2)))|v2_funct_1(k5_relat_1(X1,X2))|~v2_funct_1(X2)|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_22]), c_0_15]), c_0_16])).
% 0.19/0.38  fof(c_0_32, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X1)&v2_funct_1(X2))=>v2_funct_1(k5_relat_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t46_funct_1])).
% 0.19/0.38  cnf(c_0_33, plain, (X1=esk1_1(k5_relat_1(X2,X3))|v2_funct_1(k5_relat_1(X2,X3))|k1_funct_1(X2,X1)!=k1_funct_1(X2,esk2_1(k5_relat_1(X2,X3)))|~r2_hidden(X1,k1_relat_1(X2))|~v2_funct_1(X2)|~v2_funct_1(X3)|~v1_funct_1(X2)|~v1_funct_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.38  cnf(c_0_34, plain, (r2_hidden(esk2_1(k5_relat_1(X1,X2)),k1_relat_1(X1))|v2_funct_1(k5_relat_1(X1,X2))|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_22]), c_0_15]), c_0_16])).
% 0.19/0.38  fof(c_0_35, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&((v2_funct_1(esk3_0)&v2_funct_1(esk4_0))&~v2_funct_1(k5_relat_1(esk3_0,esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).
% 0.19/0.38  cnf(c_0_36, plain, (v2_funct_1(X1)|esk1_1(X1)!=esk2_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_37, plain, (esk1_1(k5_relat_1(X1,X2))=esk2_1(k5_relat_1(X1,X2))|v2_funct_1(k5_relat_1(X1,X2))|~v2_funct_1(X1)|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_33]), c_0_34])).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, (~v2_funct_1(k5_relat_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.38  cnf(c_0_39, plain, (v2_funct_1(k5_relat_1(X1,X2))|~v2_funct_1(X1)|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_15]), c_0_16])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.38  cnf(c_0_42, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.38  cnf(c_0_43, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 47
% 0.19/0.38  # Proof object clause steps            : 34
% 0.19/0.38  # Proof object formula steps           : 13
% 0.19/0.38  # Proof object conjectures             : 11
% 0.19/0.38  # Proof object clause conjectures      : 8
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 17
% 0.19/0.38  # Proof object initial formulas used   : 6
% 0.19/0.38  # Proof object generating inferences   : 17
% 0.19/0.38  # Proof object simplifying inferences  : 24
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 6
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 19
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 19
% 0.19/0.38  # Processed clauses                    : 59
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 4
% 0.19/0.38  # ...remaining for further processing  : 55
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 4
% 0.19/0.38  # Backward-rewritten                   : 0
% 0.19/0.38  # Generated clauses                    : 176
% 0.19/0.38  # ...of the previous two non-trivial   : 159
% 0.19/0.38  # Contextual simplify-reflections      : 40
% 0.19/0.38  # Paramodulations                      : 167
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 9
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 51
% 0.19/0.38  #    Positive orientable unit clauses  : 6
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 1
% 0.19/0.38  #    Non-unit-clauses                  : 44
% 0.19/0.38  # Current number of unprocessed clauses: 119
% 0.19/0.38  # ...number of literals in the above   : 1625
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 4
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 1461
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 237
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 48
% 0.19/0.38  # Unit Clause-clause subsumption calls : 1
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 0
% 0.19/0.38  # BW rewrite match successes           : 0
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 9493
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.038 s
% 0.19/0.38  # System time              : 0.004 s
% 0.19/0.38  # Total time               : 0.042 s
% 0.19/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
