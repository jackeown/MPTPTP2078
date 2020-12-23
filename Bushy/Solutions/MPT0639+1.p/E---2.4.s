%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t46_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:23 EDT 2019

% Result     : Theorem 15.20s
% Output     : CNFRefutation 15.20s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 142 expanded)
%              Number of clauses        :   35 (  57 expanded)
%              Number of leaves         :    6 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  301 (1038 expanded)
%              Number of equality atoms :   31 (  90 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal clause size      :   23 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/funct_1__t46_funct_1.p',t21_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/funct_1__t46_funct_1.p',d8_funct_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t46_funct_1.p',dt_k5_relat_1)).

fof(fc2_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k5_relat_1(X1,X2))
        & v1_funct_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t46_funct_1.p',fc2_funct_1)).

fof(t22_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
           => k1_funct_1(k5_relat_1(X3,X2),X1) = k1_funct_1(X2,k1_funct_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t46_funct_1.p',t22_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/funct_1__t46_funct_1.p',t46_funct_1)).

fof(c_0_6,plain,(
    ! [X19,X20,X21] :
      ( ( r2_hidden(X19,k1_relat_1(X21))
        | ~ r2_hidden(X19,k1_relat_1(k5_relat_1(X21,X20)))
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( r2_hidden(k1_funct_1(X21,X19),k1_relat_1(X20))
        | ~ r2_hidden(X19,k1_relat_1(k5_relat_1(X21,X20)))
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( ~ r2_hidden(X19,k1_relat_1(X21))
        | ~ r2_hidden(k1_funct_1(X21,X19),k1_relat_1(X20))
        | r2_hidden(X19,k1_relat_1(k5_relat_1(X21,X20)))
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_funct_1])])])])).

fof(c_0_7,plain,(
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

fof(c_0_8,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ v1_relat_1(X14)
      | v1_relat_1(k5_relat_1(X13,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_9,plain,(
    ! [X32,X33] :
      ( ( v1_relat_1(k5_relat_1(X32,X33))
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) )
      & ( v1_funct_1(k5_relat_1(X32,X33))
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).

fof(c_0_10,plain,(
    ! [X22,X23,X24] :
      ( ~ v1_relat_1(X23)
      | ~ v1_funct_1(X23)
      | ~ v1_relat_1(X24)
      | ~ v1_funct_1(X24)
      | ~ r2_hidden(X22,k1_relat_1(k5_relat_1(X24,X23)))
      | k1_funct_1(k5_relat_1(X24,X23),X22) = k1_funct_1(X23,k1_funct_1(X24,X22)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).

cnf(c_0_11,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k1_relat_1(X3))
    | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X1,X3)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( r2_hidden(esk4_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k1_funct_1(k5_relat_1(X2,X1),X3) = k1_funct_1(X1,k1_funct_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( X2 = X3
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( r2_hidden(k1_funct_1(X1,esk4_1(k5_relat_1(X1,X2))),k1_relat_1(X2))
    | v2_funct_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(esk3_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,plain,
    ( k1_funct_1(X1,esk3_1(X1)) = k1_funct_1(X1,esk4_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,plain,
    ( k1_funct_1(k5_relat_1(X1,X2),esk4_1(k5_relat_1(X1,X2))) = k1_funct_1(X2,k1_funct_1(X1,esk4_1(k5_relat_1(X1,X2))))
    | v2_funct_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_12]),c_0_13]),c_0_14])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,plain,
    ( X1 = k1_funct_1(X2,esk4_1(k5_relat_1(X2,X3)))
    | v2_funct_1(k5_relat_1(X2,X3))
    | k1_funct_1(X3,X1) != k1_funct_1(X3,k1_funct_1(X2,esk4_1(k5_relat_1(X2,X3))))
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(k1_funct_1(X1,esk3_1(k5_relat_1(X1,X2))),k1_relat_1(X2))
    | v2_funct_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_18]),c_0_13]),c_0_14])).

cnf(c_0_24,plain,
    ( k1_funct_1(k5_relat_1(X1,X2),esk3_1(k5_relat_1(X1,X2))) = k1_funct_1(X2,k1_funct_1(X1,esk3_1(k5_relat_1(X1,X2))))
    | v2_funct_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_18]),c_0_13]),c_0_14])).

cnf(c_0_25,plain,
    ( k1_funct_1(k5_relat_1(X1,X2),esk3_1(k5_relat_1(X1,X2))) = k1_funct_1(X2,k1_funct_1(X1,esk4_1(k5_relat_1(X1,X2))))
    | v2_funct_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_13]),c_0_14])).

cnf(c_0_26,plain,
    ( r2_hidden(esk4_1(k5_relat_1(X1,X2)),k1_relat_1(X1))
    | v2_funct_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_12]),c_0_13]),c_0_14])).

cnf(c_0_27,plain,
    ( k1_funct_1(X1,esk3_1(k5_relat_1(X1,X2))) = k1_funct_1(X3,esk4_1(k5_relat_1(X3,X2)))
    | v2_funct_1(k5_relat_1(X1,X2))
    | v2_funct_1(k5_relat_1(X3,X2))
    | k1_funct_1(X2,k1_funct_1(X1,esk3_1(k5_relat_1(X1,X2)))) != k1_funct_1(X2,k1_funct_1(X3,esk4_1(k5_relat_1(X3,X2))))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( k1_funct_1(X1,k1_funct_1(X2,esk4_1(k5_relat_1(X2,X1)))) = k1_funct_1(X1,k1_funct_1(X2,esk3_1(k5_relat_1(X2,X1))))
    | v2_funct_1(k5_relat_1(X2,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( X1 = esk4_1(k5_relat_1(X2,X3))
    | v2_funct_1(k5_relat_1(X2,X3))
    | k1_funct_1(X2,X1) != k1_funct_1(X2,esk4_1(k5_relat_1(X2,X3)))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_26])).

cnf(c_0_30,plain,
    ( r2_hidden(esk3_1(k5_relat_1(X1,X2)),k1_relat_1(X1))
    | v2_funct_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_18]),c_0_13]),c_0_14])).

cnf(c_0_31,plain,
    ( k1_funct_1(X1,esk3_1(k5_relat_1(X1,X2))) = k1_funct_1(X3,esk4_1(k5_relat_1(X3,X2)))
    | v2_funct_1(k5_relat_1(X3,X2))
    | v2_funct_1(k5_relat_1(X1,X2))
    | k1_funct_1(X2,k1_funct_1(X1,esk3_1(k5_relat_1(X1,X2)))) != k1_funct_1(X2,k1_funct_1(X3,esk3_1(k5_relat_1(X3,X2))))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( esk3_1(k5_relat_1(X1,X2)) = esk4_1(k5_relat_1(X1,X3))
    | v2_funct_1(k5_relat_1(X1,X2))
    | v2_funct_1(k5_relat_1(X1,X3))
    | k1_funct_1(X1,esk3_1(k5_relat_1(X1,X2))) != k1_funct_1(X1,esk4_1(k5_relat_1(X1,X3)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,plain,
    ( k1_funct_1(X1,esk4_1(k5_relat_1(X1,X2))) = k1_funct_1(X1,esk3_1(k5_relat_1(X1,X2)))
    | v2_funct_1(k5_relat_1(X1,X2))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_31])).

fof(c_0_34,negated_conjecture,(
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

cnf(c_0_35,plain,
    ( esk3_1(k5_relat_1(X1,X2)) = esk4_1(k5_relat_1(X1,X3))
    | v2_funct_1(k5_relat_1(X1,X3))
    | v2_funct_1(k5_relat_1(X1,X2))
    | k1_funct_1(X1,esk3_1(k5_relat_1(X1,X2))) != k1_funct_1(X1,esk3_1(k5_relat_1(X1,X3)))
    | ~ v2_funct_1(X1)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_36,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & v2_funct_1(esk1_0)
    & v2_funct_1(esk2_0)
    & ~ v2_funct_1(k5_relat_1(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_34])])])).

cnf(c_0_37,plain,
    ( v2_funct_1(X1)
    | esk3_1(X1) != esk4_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_38,plain,
    ( esk4_1(k5_relat_1(X1,X2)) = esk3_1(k5_relat_1(X1,X2))
    | v2_funct_1(k5_relat_1(X1,X2))
    | ~ v2_funct_1(X1)
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( ~ v2_funct_1(k5_relat_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_40,plain,
    ( v2_funct_1(k5_relat_1(X1,X2))
    | ~ v2_funct_1(X1)
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_13]),c_0_14])).

cnf(c_0_41,negated_conjecture,
    ( v2_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( v2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])]),
    [proof]).
%------------------------------------------------------------------------------
