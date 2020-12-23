%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t61_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:25 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 104 expanded)
%              Number of clauses        :   28 (  43 expanded)
%              Number of leaves         :    9 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :  245 ( 557 expanded)
%              Number of equality atoms :   61 ( 151 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal clause size      :   19 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( X2 = k6_relat_1(X1)
      <=> ( k1_relat_1(X2) = X1
          & ! [X3] :
              ( r2_hidden(X3,X1)
             => k1_funct_1(X2,X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t61_funct_1.p',t34_funct_1)).

fof(t59_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k1_relat_1(k5_relat_1(k2_funct_1(X1),X1)) = k2_relat_1(X1)
          & k2_relat_1(k5_relat_1(k2_funct_1(X1),X1)) = k2_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t61_funct_1.p',t59_funct_1)).

fof(t57_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & r2_hidden(X1,k2_relat_1(X2)) )
       => ( X1 = k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))
          & X1 = k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t61_funct_1.p',t57_funct_1)).

fof(t58_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k1_relat_1(k5_relat_1(X1,k2_funct_1(X1))) = k1_relat_1(X1)
          & k2_relat_1(k5_relat_1(X1,k2_funct_1(X1))) = k1_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t61_funct_1.p',t58_funct_1)).

fof(t56_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & r2_hidden(X1,k1_relat_1(X2)) )
       => ( X1 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))
          & X1 = k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t61_funct_1.p',t56_funct_1)).

fof(fc2_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k5_relat_1(X1,X2))
        & v1_funct_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t61_funct_1.p',fc2_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t61_funct_1.p',dt_k2_funct_1)).

fof(t61_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t61_funct_1.p',t61_funct_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t61_funct_1.p',dt_k5_relat_1)).

fof(c_0_9,plain,(
    ! [X17,X18,X19] :
      ( ( k1_relat_1(X18) = X17
        | X18 != k6_relat_1(X17)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( ~ r2_hidden(X19,X17)
        | k1_funct_1(X18,X19) = X19
        | X18 != k6_relat_1(X17)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( r2_hidden(esk3_2(X17,X18),X17)
        | k1_relat_1(X18) != X17
        | X18 = k6_relat_1(X17)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( k1_funct_1(X18,esk3_2(X17,X18)) != esk3_2(X17,X18)
        | k1_relat_1(X18) != X17
        | X18 = k6_relat_1(X17)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).

cnf(c_0_10,plain,
    ( X1 = k6_relat_1(X2)
    | k1_funct_1(X1,esk3_2(X2,X1)) != esk3_2(X2,X1)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_11,plain,(
    ! [X26] :
      ( ( k1_relat_1(k5_relat_1(k2_funct_1(X26),X26)) = k2_relat_1(X26)
        | ~ v2_funct_1(X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( k2_relat_1(k5_relat_1(k2_funct_1(X26),X26)) = k2_relat_1(X26)
        | ~ v2_funct_1(X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_funct_1])])])).

cnf(c_0_12,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | k1_funct_1(X1,esk3_2(k1_relat_1(X1),X1)) != esk3_2(k1_relat_1(X1),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(X1),X1)) = k2_relat_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X23,X24] :
      ( ( X23 = k1_funct_1(X24,k1_funct_1(k2_funct_1(X24),X23))
        | ~ v2_funct_1(X24)
        | ~ r2_hidden(X23,k2_relat_1(X24))
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( X23 = k1_funct_1(k5_relat_1(k2_funct_1(X24),X24),X23)
        | ~ v2_funct_1(X24)
        | ~ r2_hidden(X23,k2_relat_1(X24))
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_funct_1])])])).

fof(c_0_15,plain,(
    ! [X25] :
      ( ( k1_relat_1(k5_relat_1(X25,k2_funct_1(X25))) = k1_relat_1(X25)
        | ~ v2_funct_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( k2_relat_1(k5_relat_1(X25,k2_funct_1(X25))) = k1_relat_1(X25)
        | ~ v2_funct_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t58_funct_1])])])).

cnf(c_0_16,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | X2 = k6_relat_1(X1)
    | k1_relat_1(X2) != X1
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),esk3_2(k2_relat_1(X1),k5_relat_1(k2_funct_1(X1),X1))) != esk3_2(k2_relat_1(X1),k5_relat_1(k2_funct_1(X1),X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k5_relat_1(k2_funct_1(X1),X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k5_relat_1(k2_funct_1(X1),X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( X1 = k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1)
    | ~ v2_funct_1(X2)
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k1_relat_1(k5_relat_1(X1,k2_funct_1(X1))) = k1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X21,X22] :
      ( ( X21 = k1_funct_1(k2_funct_1(X22),k1_funct_1(X22,X21))
        | ~ v2_funct_1(X22)
        | ~ r2_hidden(X21,k1_relat_1(X22))
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( X21 = k1_funct_1(k5_relat_1(X22,k2_funct_1(X22)),X21)
        | ~ v2_funct_1(X22)
        | ~ r2_hidden(X21,k1_relat_1(X22))
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_funct_1])])])).

cnf(c_0_21,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | r2_hidden(esk3_2(k1_relat_1(X1),X1),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | ~ r2_hidden(esk3_2(k2_relat_1(X1),k5_relat_1(k2_funct_1(X1),X1)),k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k5_relat_1(k2_funct_1(X1),X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k5_relat_1(k2_funct_1(X1),X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_23,plain,(
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

fof(c_0_24,plain,(
    ! [X7] :
      ( ( v1_relat_1(k2_funct_1(X7))
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( v1_funct_1(k2_funct_1(X7))
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_25,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),esk3_2(k1_relat_1(X1),k5_relat_1(X1,k2_funct_1(X1)))) != esk3_2(k1_relat_1(X1),k5_relat_1(X1,k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k5_relat_1(X1,k2_funct_1(X1)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k5_relat_1(X1,k2_funct_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_19])).

cnf(c_0_26,plain,
    ( X1 = k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1)
    | ~ v2_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
            & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t61_funct_1])).

cnf(c_0_28,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k5_relat_1(k2_funct_1(X1),X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k5_relat_1(k2_funct_1(X1),X1))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_13]),c_0_22])).

cnf(c_0_29,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_32,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X8)
      | ~ v1_relat_1(X9)
      | v1_relat_1(k5_relat_1(X8,X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_33,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ r2_hidden(esk3_2(k1_relat_1(X1),k5_relat_1(X1,k2_funct_1(X1))),k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k5_relat_1(X1,k2_funct_1(X1)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k5_relat_1(X1,k2_funct_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_34,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & v2_funct_1(esk1_0)
    & ( k5_relat_1(esk1_0,k2_funct_1(esk1_0)) != k6_relat_1(k1_relat_1(esk1_0))
      | k5_relat_1(k2_funct_1(esk1_0),esk1_0) != k6_relat_1(k2_relat_1(esk1_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

cnf(c_0_35,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k5_relat_1(k2_funct_1(X1),X1))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_36,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k5_relat_1(X1,k2_funct_1(X1)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k5_relat_1(X1,k2_funct_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_19]),c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( k5_relat_1(esk1_0,k2_funct_1(esk1_0)) != k6_relat_1(k1_relat_1(esk1_0))
    | k5_relat_1(k2_funct_1(esk1_0),esk1_0) != k6_relat_1(k2_relat_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( v2_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k5_relat_1(X1,k2_funct_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( k5_relat_1(esk1_0,k2_funct_1(esk1_0)) != k6_relat_1(k1_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41]),c_0_42])])).

cnf(c_0_45,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_36]),c_0_30])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_40]),c_0_41]),c_0_42])]),
    [proof]).
%------------------------------------------------------------------------------
