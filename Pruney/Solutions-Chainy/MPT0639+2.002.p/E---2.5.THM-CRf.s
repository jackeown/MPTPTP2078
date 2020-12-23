%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:39 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 147 expanded)
%              Number of clauses        :   32 (  58 expanded)
%              Number of leaves         :    6 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  279 (1092 expanded)
%              Number of equality atoms :   30 (  89 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(fc2_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k5_relat_1(X1,X2))
        & v1_funct_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

fof(t23_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(X2))
           => k1_funct_1(k5_relat_1(X2,X3),X1) = k1_funct_1(X3,k1_funct_1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_1)).

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
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | ~ v1_relat_1(X5)
      | v1_relat_1(k5_relat_1(X4,X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_9,plain,(
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

cnf(c_0_10,plain,
    ( X2 = X3
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k1_relat_1(X3))
    | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X1,X3)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,plain,(
    ! [X16,X17,X18] :
      ( ~ v1_relat_1(X17)
      | ~ v1_funct_1(X17)
      | ~ v1_relat_1(X18)
      | ~ v1_funct_1(X18)
      | ~ r2_hidden(X16,k1_relat_1(X17))
      | k1_funct_1(k5_relat_1(X17,X18),X16) = k1_funct_1(X18,k1_funct_1(X17,X16)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

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
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

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
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_18,plain,
    ( k1_funct_1(X1,esk1_1(X1)) = k1_funct_1(X1,esk2_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,plain,
    ( k1_funct_1(k5_relat_1(X1,X2),X3) = k1_funct_1(X2,k1_funct_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_1(k5_relat_1(X1,X2)),k1_relat_1(X1))
    | v2_funct_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])).

cnf(c_0_21,plain,
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

cnf(c_0_22,plain,
    ( k1_funct_1(X1,k1_funct_1(X2,esk1_1(k5_relat_1(X2,X1)))) = k1_funct_1(k5_relat_1(X2,X1),esk2_1(k5_relat_1(X2,X1)))
    | v2_funct_1(k5_relat_1(X2,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_15]),c_0_16]),c_0_20])).

cnf(c_0_23,plain,
    ( r2_hidden(esk2_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,plain,
    ( X1 = k1_funct_1(X2,esk1_1(k5_relat_1(X2,X3)))
    | v2_funct_1(k5_relat_1(X2,X3))
    | k1_funct_1(X3,X1) != k1_funct_1(k5_relat_1(X2,X3),esk2_1(k5_relat_1(X2,X3)))
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,plain,
    ( r2_hidden(esk2_1(k5_relat_1(X1,X2)),k1_relat_1(X1))
    | v2_funct_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_23]),c_0_15]),c_0_16])).

cnf(c_0_26,plain,
    ( X1 = k1_funct_1(X2,esk1_1(k5_relat_1(X2,X3)))
    | v2_funct_1(k5_relat_1(X2,X3))
    | k1_funct_1(X3,X1) != k1_funct_1(X3,k1_funct_1(X2,esk2_1(k5_relat_1(X2,X3))))
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_19]),c_0_25])).

cnf(c_0_27,plain,
    ( k1_funct_1(X1,esk1_1(k5_relat_1(X1,X2))) = k1_funct_1(X1,esk2_1(k5_relat_1(X1,X2)))
    | v2_funct_1(k5_relat_1(X1,X2))
    | ~ r2_hidden(k1_funct_1(X1,esk2_1(k5_relat_1(X1,X2))),k1_relat_1(X2))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_28,plain,
    ( k1_funct_1(X1,esk1_1(k5_relat_1(X1,X2))) = k1_funct_1(X1,esk2_1(k5_relat_1(X1,X2)))
    | v2_funct_1(k5_relat_1(X1,X2))
    | ~ r2_hidden(esk2_1(k5_relat_1(X1,X2)),k1_relat_1(k5_relat_1(X1,X2)))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_11])).

cnf(c_0_29,plain,
    ( X1 = esk1_1(k5_relat_1(X2,X3))
    | v2_funct_1(k5_relat_1(X2,X3))
    | k1_funct_1(X2,X1) != k1_funct_1(X2,esk1_1(k5_relat_1(X2,X3)))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_10,c_0_20])).

cnf(c_0_30,plain,
    ( k1_funct_1(X1,esk1_1(k5_relat_1(X1,X2))) = k1_funct_1(X1,esk2_1(k5_relat_1(X1,X2)))
    | v2_funct_1(k5_relat_1(X1,X2))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_23]),c_0_15]),c_0_16])).

fof(c_0_31,negated_conjecture,(
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

cnf(c_0_32,plain,
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
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_33,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & v2_funct_1(esk3_0)
    & v2_funct_1(esk4_0)
    & ~ v2_funct_1(k5_relat_1(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

cnf(c_0_34,plain,
    ( v2_funct_1(X1)
    | esk1_1(X1) != esk2_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_35,plain,
    ( esk1_1(k5_relat_1(X1,X2)) = esk2_1(k5_relat_1(X1,X2))
    | v2_funct_1(k5_relat_1(X1,X2))
    | ~ v2_funct_1(X1)
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_32]),c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_funct_1(k5_relat_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,plain,
    ( v2_funct_1(k5_relat_1(X1,X2))
    | ~ v2_funct_1(X1)
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_15]),c_0_16])).

cnf(c_0_38,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:06:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.39  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_AE_CS_SP_PI_S0Y
% 0.12/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.39  #
% 0.12/0.39  # Preprocessing time       : 0.027 s
% 0.12/0.39  
% 0.12/0.39  # Proof found!
% 0.12/0.39  # SZS status Theorem
% 0.12/0.39  # SZS output start CNFRefutation
% 0.12/0.39  fof(d8_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)<=>![X2, X3]:(((r2_hidden(X2,k1_relat_1(X1))&r2_hidden(X3,k1_relat_1(X1)))&k1_funct_1(X1,X2)=k1_funct_1(X1,X3))=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 0.12/0.39  fof(t21_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_funct_1)).
% 0.12/0.39  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.12/0.39  fof(fc2_funct_1, axiom, ![X1, X2]:((((v1_relat_1(X1)&v1_funct_1(X1))&v1_relat_1(X2))&v1_funct_1(X2))=>(v1_relat_1(k5_relat_1(X1,X2))&v1_funct_1(k5_relat_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funct_1)).
% 0.12/0.39  fof(t23_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(X2))=>k1_funct_1(k5_relat_1(X2,X3),X1)=k1_funct_1(X3,k1_funct_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 0.12/0.39  fof(t46_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X1)&v2_funct_1(X2))=>v2_funct_1(k5_relat_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_funct_1)).
% 0.12/0.39  fof(c_0_6, plain, ![X6, X7, X8]:((~v2_funct_1(X6)|(~r2_hidden(X7,k1_relat_1(X6))|~r2_hidden(X8,k1_relat_1(X6))|k1_funct_1(X6,X7)!=k1_funct_1(X6,X8)|X7=X8)|(~v1_relat_1(X6)|~v1_funct_1(X6)))&((((r2_hidden(esk1_1(X6),k1_relat_1(X6))|v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6)))&(r2_hidden(esk2_1(X6),k1_relat_1(X6))|v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6))))&(k1_funct_1(X6,esk1_1(X6))=k1_funct_1(X6,esk2_1(X6))|v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6))))&(esk1_1(X6)!=esk2_1(X6)|v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).
% 0.12/0.39  fof(c_0_7, plain, ![X13, X14, X15]:(((r2_hidden(X13,k1_relat_1(X15))|~r2_hidden(X13,k1_relat_1(k5_relat_1(X15,X14)))|(~v1_relat_1(X15)|~v1_funct_1(X15))|(~v1_relat_1(X14)|~v1_funct_1(X14)))&(r2_hidden(k1_funct_1(X15,X13),k1_relat_1(X14))|~r2_hidden(X13,k1_relat_1(k5_relat_1(X15,X14)))|(~v1_relat_1(X15)|~v1_funct_1(X15))|(~v1_relat_1(X14)|~v1_funct_1(X14))))&(~r2_hidden(X13,k1_relat_1(X15))|~r2_hidden(k1_funct_1(X15,X13),k1_relat_1(X14))|r2_hidden(X13,k1_relat_1(k5_relat_1(X15,X14)))|(~v1_relat_1(X15)|~v1_funct_1(X15))|(~v1_relat_1(X14)|~v1_funct_1(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_funct_1])])])])).
% 0.12/0.39  fof(c_0_8, plain, ![X4, X5]:(~v1_relat_1(X4)|~v1_relat_1(X5)|v1_relat_1(k5_relat_1(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.12/0.39  fof(c_0_9, plain, ![X11, X12]:((v1_relat_1(k5_relat_1(X11,X12))|(~v1_relat_1(X11)|~v1_funct_1(X11)|~v1_relat_1(X12)|~v1_funct_1(X12)))&(v1_funct_1(k5_relat_1(X11,X12))|(~v1_relat_1(X11)|~v1_funct_1(X11)|~v1_relat_1(X12)|~v1_funct_1(X12)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).
% 0.12/0.39  cnf(c_0_10, plain, (X2=X3|~v2_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r2_hidden(X3,k1_relat_1(X1))|k1_funct_1(X1,X2)!=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.39  cnf(c_0_11, plain, (r2_hidden(k1_funct_1(X1,X2),k1_relat_1(X3))|~r2_hidden(X2,k1_relat_1(k5_relat_1(X1,X3)))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X3)|~v1_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.39  fof(c_0_12, plain, ![X16, X17, X18]:(~v1_relat_1(X17)|~v1_funct_1(X17)|(~v1_relat_1(X18)|~v1_funct_1(X18)|(~r2_hidden(X16,k1_relat_1(X17))|k1_funct_1(k5_relat_1(X17,X18),X16)=k1_funct_1(X18,k1_funct_1(X17,X16))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).
% 0.12/0.39  cnf(c_0_13, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X3)|~v1_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.39  cnf(c_0_14, plain, (r2_hidden(esk1_1(X1),k1_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.39  cnf(c_0_15, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.39  cnf(c_0_16, plain, (v1_funct_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.39  cnf(c_0_17, plain, (X1=k1_funct_1(X2,X3)|k1_funct_1(X4,X1)!=k1_funct_1(X4,k1_funct_1(X2,X3))|~r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X4)))|~r2_hidden(X1,k1_relat_1(X4))|~v2_funct_1(X4)|~v1_funct_1(X4)|~v1_funct_1(X2)|~v1_relat_1(X4)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.12/0.39  cnf(c_0_18, plain, (k1_funct_1(X1,esk1_1(X1))=k1_funct_1(X1,esk2_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.39  cnf(c_0_19, plain, (k1_funct_1(k5_relat_1(X1,X2),X3)=k1_funct_1(X2,k1_funct_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.39  cnf(c_0_20, plain, (r2_hidden(esk1_1(k5_relat_1(X1,X2)),k1_relat_1(X1))|v2_funct_1(k5_relat_1(X1,X2))|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16])).
% 0.12/0.39  cnf(c_0_21, plain, (X1=k1_funct_1(X2,esk1_1(k5_relat_1(X2,X3)))|v2_funct_1(k5_relat_1(X2,X3))|k1_funct_1(X3,X1)!=k1_funct_1(X3,k1_funct_1(X2,esk1_1(k5_relat_1(X2,X3))))|~r2_hidden(X1,k1_relat_1(X3))|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_1(X2)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_14]), c_0_15]), c_0_16])).
% 0.12/0.39  cnf(c_0_22, plain, (k1_funct_1(X1,k1_funct_1(X2,esk1_1(k5_relat_1(X2,X1))))=k1_funct_1(k5_relat_1(X2,X1),esk2_1(k5_relat_1(X2,X1)))|v2_funct_1(k5_relat_1(X2,X1))|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_15]), c_0_16]), c_0_20])).
% 0.12/0.39  cnf(c_0_23, plain, (r2_hidden(esk2_1(X1),k1_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.39  cnf(c_0_24, plain, (X1=k1_funct_1(X2,esk1_1(k5_relat_1(X2,X3)))|v2_funct_1(k5_relat_1(X2,X3))|k1_funct_1(X3,X1)!=k1_funct_1(k5_relat_1(X2,X3),esk2_1(k5_relat_1(X2,X3)))|~r2_hidden(X1,k1_relat_1(X3))|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_1(X2)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.12/0.39  cnf(c_0_25, plain, (r2_hidden(esk2_1(k5_relat_1(X1,X2)),k1_relat_1(X1))|v2_funct_1(k5_relat_1(X1,X2))|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_23]), c_0_15]), c_0_16])).
% 0.12/0.39  cnf(c_0_26, plain, (X1=k1_funct_1(X2,esk1_1(k5_relat_1(X2,X3)))|v2_funct_1(k5_relat_1(X2,X3))|k1_funct_1(X3,X1)!=k1_funct_1(X3,k1_funct_1(X2,esk2_1(k5_relat_1(X2,X3))))|~r2_hidden(X1,k1_relat_1(X3))|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_1(X2)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_19]), c_0_25])).
% 0.12/0.39  cnf(c_0_27, plain, (k1_funct_1(X1,esk1_1(k5_relat_1(X1,X2)))=k1_funct_1(X1,esk2_1(k5_relat_1(X1,X2)))|v2_funct_1(k5_relat_1(X1,X2))|~r2_hidden(k1_funct_1(X1,esk2_1(k5_relat_1(X1,X2))),k1_relat_1(X2))|~v2_funct_1(X2)|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_26])).
% 0.12/0.39  cnf(c_0_28, plain, (k1_funct_1(X1,esk1_1(k5_relat_1(X1,X2)))=k1_funct_1(X1,esk2_1(k5_relat_1(X1,X2)))|v2_funct_1(k5_relat_1(X1,X2))|~r2_hidden(esk2_1(k5_relat_1(X1,X2)),k1_relat_1(k5_relat_1(X1,X2)))|~v2_funct_1(X2)|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_27, c_0_11])).
% 0.12/0.39  cnf(c_0_29, plain, (X1=esk1_1(k5_relat_1(X2,X3))|v2_funct_1(k5_relat_1(X2,X3))|k1_funct_1(X2,X1)!=k1_funct_1(X2,esk1_1(k5_relat_1(X2,X3)))|~r2_hidden(X1,k1_relat_1(X2))|~v2_funct_1(X2)|~v1_funct_1(X2)|~v1_funct_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_10, c_0_20])).
% 0.12/0.39  cnf(c_0_30, plain, (k1_funct_1(X1,esk1_1(k5_relat_1(X1,X2)))=k1_funct_1(X1,esk2_1(k5_relat_1(X1,X2)))|v2_funct_1(k5_relat_1(X1,X2))|~v2_funct_1(X2)|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_23]), c_0_15]), c_0_16])).
% 0.12/0.39  fof(c_0_31, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X1)&v2_funct_1(X2))=>v2_funct_1(k5_relat_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t46_funct_1])).
% 0.12/0.39  cnf(c_0_32, plain, (X1=esk1_1(k5_relat_1(X2,X3))|v2_funct_1(k5_relat_1(X2,X3))|k1_funct_1(X2,X1)!=k1_funct_1(X2,esk2_1(k5_relat_1(X2,X3)))|~r2_hidden(X1,k1_relat_1(X2))|~v2_funct_1(X2)|~v2_funct_1(X3)|~v1_funct_1(X2)|~v1_funct_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.12/0.39  fof(c_0_33, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&((v2_funct_1(esk3_0)&v2_funct_1(esk4_0))&~v2_funct_1(k5_relat_1(esk3_0,esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).
% 0.12/0.39  cnf(c_0_34, plain, (v2_funct_1(X1)|esk1_1(X1)!=esk2_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.39  cnf(c_0_35, plain, (esk1_1(k5_relat_1(X1,X2))=esk2_1(k5_relat_1(X1,X2))|v2_funct_1(k5_relat_1(X1,X2))|~v2_funct_1(X1)|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_32]), c_0_25])).
% 0.12/0.39  cnf(c_0_36, negated_conjecture, (~v2_funct_1(k5_relat_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.39  cnf(c_0_37, plain, (v2_funct_1(k5_relat_1(X1,X2))|~v2_funct_1(X1)|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_15]), c_0_16])).
% 0.12/0.39  cnf(c_0_38, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.39  cnf(c_0_39, negated_conjecture, (v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.39  cnf(c_0_40, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.39  cnf(c_0_41, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.39  cnf(c_0_42, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.39  cnf(c_0_43, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.39  cnf(c_0_44, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43])]), ['proof']).
% 0.12/0.39  # SZS output end CNFRefutation
% 0.12/0.39  # Proof object total steps             : 45
% 0.12/0.39  # Proof object clause steps            : 32
% 0.12/0.39  # Proof object formula steps           : 13
% 0.12/0.39  # Proof object conjectures             : 11
% 0.12/0.39  # Proof object clause conjectures      : 8
% 0.12/0.39  # Proof object formula conjectures     : 3
% 0.12/0.39  # Proof object initial clauses used    : 17
% 0.12/0.39  # Proof object initial formulas used   : 6
% 0.12/0.39  # Proof object generating inferences   : 15
% 0.12/0.39  # Proof object simplifying inferences  : 22
% 0.12/0.39  # Training examples: 0 positive, 0 negative
% 0.12/0.39  # Parsed axioms                        : 6
% 0.12/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.39  # Initial clauses                      : 19
% 0.12/0.39  # Removed in clause preprocessing      : 0
% 0.12/0.39  # Initial clauses in saturation        : 19
% 0.12/0.39  # Processed clauses                    : 71
% 0.12/0.39  # ...of these trivial                  : 0
% 0.12/0.39  # ...subsumed                          : 5
% 0.12/0.39  # ...remaining for further processing  : 66
% 0.12/0.39  # Other redundant clauses eliminated   : 0
% 0.12/0.39  # Clauses deleted for lack of memory   : 0
% 0.12/0.39  # Backward-subsumed                    : 4
% 0.12/0.39  # Backward-rewritten                   : 0
% 0.12/0.39  # Generated clauses                    : 311
% 0.12/0.39  # ...of the previous two non-trivial   : 287
% 0.12/0.39  # Contextual simplify-reflections      : 50
% 0.12/0.39  # Paramodulations                      : 302
% 0.12/0.39  # Factorizations                       : 0
% 0.12/0.39  # Equation resolutions                 : 9
% 0.12/0.39  # Propositional unsat checks           : 0
% 0.12/0.39  #    Propositional check models        : 0
% 0.12/0.39  #    Propositional check unsatisfiable : 0
% 0.12/0.39  #    Propositional clauses             : 0
% 0.12/0.39  #    Propositional clauses after purity: 0
% 0.12/0.39  #    Propositional unsat core size     : 0
% 0.12/0.39  #    Propositional preprocessing time  : 0.000
% 0.12/0.39  #    Propositional encoding time       : 0.000
% 0.12/0.39  #    Propositional solver time         : 0.000
% 0.12/0.39  #    Success case prop preproc time    : 0.000
% 0.12/0.39  #    Success case prop encoding time   : 0.000
% 0.12/0.39  #    Success case prop solver time     : 0.000
% 0.12/0.39  # Current number of processed clauses  : 62
% 0.12/0.39  #    Positive orientable unit clauses  : 6
% 0.12/0.39  #    Positive unorientable unit clauses: 0
% 0.12/0.39  #    Negative unit clauses             : 1
% 0.12/0.39  #    Non-unit-clauses                  : 55
% 0.12/0.39  # Current number of unprocessed clauses: 235
% 0.12/0.39  # ...number of literals in the above   : 3413
% 0.12/0.39  # Current number of archived formulas  : 0
% 0.12/0.39  # Current number of archived clauses   : 4
% 0.12/0.39  # Clause-clause subsumption calls (NU) : 2480
% 0.12/0.39  # Rec. Clause-clause subsumption calls : 582
% 0.12/0.39  # Non-unit clause-clause subsumptions  : 59
% 0.12/0.39  # Unit Clause-clause subsumption calls : 1
% 0.12/0.39  # Rewrite failures with RHS unbound    : 0
% 0.12/0.39  # BW rewrite match attempts            : 0
% 0.12/0.39  # BW rewrite match successes           : 0
% 0.12/0.39  # Condensation attempts                : 0
% 0.12/0.39  # Condensation successes               : 0
% 0.12/0.39  # Termbank termtop insertions          : 16254
% 0.12/0.39  
% 0.12/0.39  # -------------------------------------------------
% 0.12/0.39  # User time                : 0.047 s
% 0.12/0.39  # System time              : 0.004 s
% 0.12/0.39  # Total time               : 0.051 s
% 0.12/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
