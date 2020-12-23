%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:58 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 474 expanded)
%              Number of clauses        :   51 ( 179 expanded)
%              Number of leaves         :   13 ( 125 expanded)
%              Depth                    :   10
%              Number of atoms          :  261 (2574 expanded)
%              Number of equality atoms :   81 ( 978 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t60_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & k1_relat_1(X1) = k2_relat_1(X2)
              & k2_relat_1(X1) = k1_relat_1(X2)
              & ! [X3,X4] :
                  ( ( r2_hidden(X3,k1_relat_1(X1))
                    & r2_hidden(X4,k1_relat_1(X2)) )
                 => ( k1_funct_1(X1,X3) = X4
                  <=> k1_funct_1(X2,X4) = X3 ) ) )
           => X2 = k2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_1)).

fof(t54_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(involutiveness_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k4_relat_1(k4_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(t12_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(t37_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(t72_relat_1,axiom,(
    ! [X1] : k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t56_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & r2_hidden(X1,k1_relat_1(X2)) )
       => ( X1 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))
          & X1 = k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(fc5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v2_funct_1(X1) )
     => ( v1_relat_1(k4_relat_1(X1))
        & v1_funct_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_funct_1)).

fof(t9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( k1_relat_1(X1) = k1_relat_1(X2)
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ( ( v2_funct_1(X1)
                & k1_relat_1(X1) = k2_relat_1(X2)
                & k2_relat_1(X1) = k1_relat_1(X2)
                & ! [X3,X4] :
                    ( ( r2_hidden(X3,k1_relat_1(X1))
                      & r2_hidden(X4,k1_relat_1(X2)) )
                   => ( k1_funct_1(X1,X3) = X4
                    <=> k1_funct_1(X2,X4) = X3 ) ) )
             => X2 = k2_funct_1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t60_funct_1])).

fof(c_0_14,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X8)
      | ~ v1_relat_1(X9)
      | k4_relat_1(k5_relat_1(X8,X9)) = k5_relat_1(k4_relat_1(X9),k4_relat_1(X8)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).

fof(c_0_15,plain,(
    ! [X6] :
      ( ~ v1_relat_1(X6)
      | k4_relat_1(k4_relat_1(X6)) = X6 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k4_relat_1])])).

fof(c_0_16,plain,(
    ! [X5] :
      ( ~ v1_relat_1(X5)
      | v1_relat_1(k4_relat_1(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

fof(c_0_17,negated_conjecture,(
    ! [X25,X26] :
      ( v1_relat_1(esk2_0)
      & v1_funct_1(esk2_0)
      & v1_relat_1(esk3_0)
      & v1_funct_1(esk3_0)
      & v2_funct_1(esk2_0)
      & k1_relat_1(esk2_0) = k2_relat_1(esk3_0)
      & k2_relat_1(esk2_0) = k1_relat_1(esk3_0)
      & ( k1_funct_1(esk2_0,X25) != X26
        | k1_funct_1(esk3_0,X26) = X25
        | ~ r2_hidden(X25,k1_relat_1(esk2_0))
        | ~ r2_hidden(X26,k1_relat_1(esk3_0)) )
      & ( k1_funct_1(esk3_0,X26) != X25
        | k1_funct_1(esk2_0,X25) = X26
        | ~ r2_hidden(X25,k1_relat_1(esk2_0))
        | ~ r2_hidden(X26,k1_relat_1(esk3_0)) )
      & esk3_0 != k2_funct_1(esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])])).

fof(c_0_18,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X17)
      | ~ v1_funct_1(X17)
      | ~ r2_hidden(X16,k1_relat_1(X17))
      | r2_hidden(k1_funct_1(X17,X16),k2_relat_1(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).

cnf(c_0_19,plain,
    ( k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k4_relat_1(k4_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X12] :
      ( ~ v1_relat_1(X12)
      | k5_relat_1(X12,k6_relat_1(k2_relat_1(X12))) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

fof(c_0_23,plain,(
    ! [X7] :
      ( ( k2_relat_1(X7) = k1_relat_1(k4_relat_1(X7))
        | ~ v1_relat_1(X7) )
      & ( k1_relat_1(X7) = k2_relat_1(k4_relat_1(X7))
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

cnf(c_0_24,negated_conjecture,
    ( k1_funct_1(esk2_0,X2) = X1
    | k1_funct_1(esk3_0,X1) != X2
    | ~ r2_hidden(X2,k1_relat_1(esk2_0))
    | ~ r2_hidden(X1,k1_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( k1_relat_1(esk2_0) = k2_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( k4_relat_1(k5_relat_1(k4_relat_1(X1),X2)) = k5_relat_1(k4_relat_1(X2),X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_30,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_32,plain,(
    ! [X10] : k4_relat_1(k6_relat_1(X10)) = k6_relat_1(X10) ),
    inference(variable_rename,[status(thm)],[t72_relat_1])).

fof(c_0_33,plain,(
    ! [X14] :
      ( v1_relat_1(k6_relat_1(X14))
      & v1_funct_1(k6_relat_1(X14)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_34,plain,(
    ! [X18,X19] :
      ( ( X18 = k1_funct_1(k2_funct_1(X19),k1_funct_1(X19,X18))
        | ~ v2_funct_1(X19)
        | ~ r2_hidden(X18,k1_relat_1(X19))
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( X18 = k1_funct_1(k5_relat_1(X19,k2_funct_1(X19)),X18)
        | ~ v2_funct_1(X19)
        | ~ r2_hidden(X18,k1_relat_1(X19))
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_funct_1])])])).

cnf(c_0_35,negated_conjecture,
    ( k1_funct_1(esk2_0,k1_funct_1(esk3_0,X1)) = X1
    | ~ r2_hidden(k1_funct_1(esk3_0,X1),k1_relat_1(esk2_0))
    | ~ r2_hidden(X1,k1_relat_1(esk3_0)) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk3_0,X1),k1_relat_1(esk2_0))
    | ~ r2_hidden(X1,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_37,plain,
    ( v1_relat_1(k5_relat_1(k4_relat_1(X1),X2))
    | ~ v1_relat_1(k5_relat_1(k4_relat_1(X2),X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_29])).

cnf(c_0_38,plain,
    ( k5_relat_1(k4_relat_1(X1),k6_relat_1(k1_relat_1(X1))) = k4_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_21])).

cnf(c_0_39,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( X1 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))
    | ~ v2_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( k1_funct_1(esk2_0,k1_funct_1(esk3_0,X1)) = X1
    | ~ r2_hidden(X1,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( v2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_46,plain,(
    ! [X13] :
      ( ~ v1_relat_1(X13)
      | ~ v1_funct_1(X13)
      | ~ v2_funct_1(X13)
      | k2_funct_1(X13) = k4_relat_1(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

fof(c_0_47,plain,(
    ! [X15] :
      ( ( v1_relat_1(k4_relat_1(X15))
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15)
        | ~ v2_funct_1(X15) )
      & ( v1_funct_1(k4_relat_1(X15))
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15)
        | ~ v2_funct_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc5_funct_1])])])).

cnf(c_0_48,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40])]),c_0_21])).

cnf(c_0_49,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = k4_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_50,plain,
    ( k5_relat_1(k4_relat_1(X1),k6_relat_1(X2)) = k4_relat_1(k5_relat_1(k6_relat_1(X2),X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_39]),c_0_40])])).

cnf(c_0_51,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(k4_relat_1(X1))),X1))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_30]),c_0_39]),c_0_40])]),c_0_21])).

fof(c_0_52,plain,(
    ! [X20,X21] :
      ( ( r2_hidden(esk1_2(X20,X21),k1_relat_1(X20))
        | k1_relat_1(X20) != k1_relat_1(X21)
        | X20 = X21
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( k1_funct_1(X20,esk1_2(X20,X21)) != k1_funct_1(X21,esk1_2(X20,X21))
        | k1_relat_1(X20) != k1_relat_1(X21)
        | X20 = X21
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).

cnf(c_0_53,negated_conjecture,
    ( k1_funct_1(k2_funct_1(esk2_0),X1) = k1_funct_1(esk3_0,X1)
    | ~ r2_hidden(X1,k1_relat_1(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_44]),c_0_45])]),c_0_36])).

cnf(c_0_54,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( k2_relat_1(esk2_0) = k1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_56,plain,
    ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_57,plain,
    ( v1_funct_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,plain,
    ( v1_relat_1(k4_relat_1(k4_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_59,plain,
    ( k4_relat_1(k5_relat_1(k6_relat_1(X1),k4_relat_1(X2))) = k5_relat_1(X2,k6_relat_1(X1))
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_20]),c_0_21])).

cnf(c_0_60,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(X1)),k4_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_20]),c_0_21])).

cnf(c_0_61,plain,
    ( r2_hidden(esk1_2(X1,X2),k1_relat_1(X1))
    | X1 = X2
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( esk3_0 != k2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_63,plain,
    ( X1 = X2
    | k1_funct_1(X1,esk1_2(X1,X2)) != k1_funct_1(X2,esk1_2(X1,X2))
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_64,negated_conjecture,
    ( k1_funct_1(k4_relat_1(esk2_0),X1) = k1_funct_1(esk3_0,X1)
    | ~ r2_hidden(X1,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_43]),c_0_44]),c_0_45])])).

cnf(c_0_65,negated_conjecture,
    ( k1_relat_1(k4_relat_1(esk2_0)) = k1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_45])])).

cnf(c_0_66,negated_conjecture,
    ( v1_funct_1(k4_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_43]),c_0_44]),c_0_45])])).

cnf(c_0_67,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(X1,k6_relat_1(X2))))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(X2),k4_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( v1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(esk3_0)),k4_relat_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_55]),c_0_45])])).

cnf(c_0_69,negated_conjecture,
    ( k5_relat_1(esk2_0,k6_relat_1(k1_relat_1(esk3_0))) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_55]),c_0_45])])).

cnf(c_0_70,negated_conjecture,
    ( X1 = esk3_0
    | r2_hidden(esk1_2(X1,esk3_0),k1_relat_1(X1))
    | k1_relat_1(X1) != k1_relat_1(esk3_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_27]),c_0_28])])).

cnf(c_0_71,negated_conjecture,
    ( k4_relat_1(esk2_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_54]),c_0_43]),c_0_44]),c_0_45])])).

cnf(c_0_72,negated_conjecture,
    ( k4_relat_1(esk2_0) = X1
    | k1_funct_1(esk3_0,esk1_2(k4_relat_1(esk2_0),X1)) != k1_funct_1(X1,esk1_2(k4_relat_1(esk2_0),X1))
    | k1_relat_1(esk3_0) != k1_relat_1(X1)
    | ~ r2_hidden(esk1_2(k4_relat_1(esk2_0),X1),k1_relat_1(esk3_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k4_relat_1(esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_66])])).

cnf(c_0_73,negated_conjecture,
    ( v1_relat_1(k4_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69]),c_0_45])])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk1_2(k4_relat_1(esk2_0),esk3_0),k1_relat_1(esk3_0))
    | ~ v1_relat_1(k4_relat_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_65]),c_0_66])]),c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( k4_relat_1(esk2_0) = X1
    | k1_funct_1(esk3_0,esk1_2(k4_relat_1(esk2_0),X1)) != k1_funct_1(X1,esk1_2(k4_relat_1(esk2_0),X1))
    | k1_relat_1(esk3_0) != k1_relat_1(X1)
    | ~ r2_hidden(esk1_2(k4_relat_1(esk2_0),X1),k1_relat_1(esk3_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73])])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk1_2(k4_relat_1(esk2_0),esk3_0),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_73])])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_27]),c_0_28])]),c_0_71]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:24:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.42  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.42  #
% 0.19/0.42  # Preprocessing time       : 0.028 s
% 0.19/0.42  # Presaturation interreduction done
% 0.19/0.42  
% 0.19/0.42  # Proof found!
% 0.19/0.42  # SZS status Theorem
% 0.19/0.42  # SZS output start CNFRefutation
% 0.19/0.42  fof(t60_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((((v2_funct_1(X1)&k1_relat_1(X1)=k2_relat_1(X2))&k2_relat_1(X1)=k1_relat_1(X2))&![X3, X4]:((r2_hidden(X3,k1_relat_1(X1))&r2_hidden(X4,k1_relat_1(X2)))=>(k1_funct_1(X1,X3)=X4<=>k1_funct_1(X2,X4)=X3)))=>X2=k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_1)).
% 0.19/0.42  fof(t54_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 0.19/0.42  fof(involutiveness_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k4_relat_1(k4_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 0.19/0.42  fof(dt_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>v1_relat_1(k4_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 0.19/0.42  fof(t12_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 0.19/0.42  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 0.19/0.42  fof(t37_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))&k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 0.19/0.42  fof(t72_relat_1, axiom, ![X1]:k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 0.19/0.42  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.19/0.42  fof(t56_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k1_relat_1(X2)))=>(X1=k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))&X1=k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 0.19/0.42  fof(d9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(X1)=k4_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 0.19/0.42  fof(fc5_funct_1, axiom, ![X1]:(((v1_relat_1(X1)&v1_funct_1(X1))&v2_funct_1(X1))=>(v1_relat_1(k4_relat_1(X1))&v1_funct_1(k4_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_funct_1)).
% 0.19/0.42  fof(t9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k1_relat_1(X1)=k1_relat_1(X2)&![X3]:(r2_hidden(X3,k1_relat_1(X1))=>k1_funct_1(X1,X3)=k1_funct_1(X2,X3)))=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 0.19/0.42  fof(c_0_13, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((((v2_funct_1(X1)&k1_relat_1(X1)=k2_relat_1(X2))&k2_relat_1(X1)=k1_relat_1(X2))&![X3, X4]:((r2_hidden(X3,k1_relat_1(X1))&r2_hidden(X4,k1_relat_1(X2)))=>(k1_funct_1(X1,X3)=X4<=>k1_funct_1(X2,X4)=X3)))=>X2=k2_funct_1(X1))))), inference(assume_negation,[status(cth)],[t60_funct_1])).
% 0.19/0.42  fof(c_0_14, plain, ![X8, X9]:(~v1_relat_1(X8)|(~v1_relat_1(X9)|k4_relat_1(k5_relat_1(X8,X9))=k5_relat_1(k4_relat_1(X9),k4_relat_1(X8)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).
% 0.19/0.42  fof(c_0_15, plain, ![X6]:(~v1_relat_1(X6)|k4_relat_1(k4_relat_1(X6))=X6), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k4_relat_1])])).
% 0.19/0.42  fof(c_0_16, plain, ![X5]:(~v1_relat_1(X5)|v1_relat_1(k4_relat_1(X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).
% 0.19/0.42  fof(c_0_17, negated_conjecture, ![X25, X26]:((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((((v2_funct_1(esk2_0)&k1_relat_1(esk2_0)=k2_relat_1(esk3_0))&k2_relat_1(esk2_0)=k1_relat_1(esk3_0))&((k1_funct_1(esk2_0,X25)!=X26|k1_funct_1(esk3_0,X26)=X25|(~r2_hidden(X25,k1_relat_1(esk2_0))|~r2_hidden(X26,k1_relat_1(esk3_0))))&(k1_funct_1(esk3_0,X26)!=X25|k1_funct_1(esk2_0,X25)=X26|(~r2_hidden(X25,k1_relat_1(esk2_0))|~r2_hidden(X26,k1_relat_1(esk3_0))))))&esk3_0!=k2_funct_1(esk2_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])])).
% 0.19/0.42  fof(c_0_18, plain, ![X16, X17]:(~v1_relat_1(X17)|~v1_funct_1(X17)|(~r2_hidden(X16,k1_relat_1(X17))|r2_hidden(k1_funct_1(X17,X16),k2_relat_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).
% 0.19/0.42  cnf(c_0_19, plain, (k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.42  cnf(c_0_20, plain, (k4_relat_1(k4_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.42  cnf(c_0_21, plain, (v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.42  fof(c_0_22, plain, ![X12]:(~v1_relat_1(X12)|k5_relat_1(X12,k6_relat_1(k2_relat_1(X12)))=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 0.19/0.42  fof(c_0_23, plain, ![X7]:((k2_relat_1(X7)=k1_relat_1(k4_relat_1(X7))|~v1_relat_1(X7))&(k1_relat_1(X7)=k2_relat_1(k4_relat_1(X7))|~v1_relat_1(X7))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).
% 0.19/0.42  cnf(c_0_24, negated_conjecture, (k1_funct_1(esk2_0,X2)=X1|k1_funct_1(esk3_0,X1)!=X2|~r2_hidden(X2,k1_relat_1(esk2_0))|~r2_hidden(X1,k1_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.42  cnf(c_0_25, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.42  cnf(c_0_26, negated_conjecture, (k1_relat_1(esk2_0)=k2_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.42  cnf(c_0_27, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.42  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.42  cnf(c_0_29, plain, (k4_relat_1(k5_relat_1(k4_relat_1(X1),X2))=k5_relat_1(k4_relat_1(X2),X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.19/0.42  cnf(c_0_30, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.42  cnf(c_0_31, plain, (k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.42  fof(c_0_32, plain, ![X10]:k4_relat_1(k6_relat_1(X10))=k6_relat_1(X10), inference(variable_rename,[status(thm)],[t72_relat_1])).
% 0.19/0.42  fof(c_0_33, plain, ![X14]:(v1_relat_1(k6_relat_1(X14))&v1_funct_1(k6_relat_1(X14))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.19/0.42  fof(c_0_34, plain, ![X18, X19]:((X18=k1_funct_1(k2_funct_1(X19),k1_funct_1(X19,X18))|(~v2_funct_1(X19)|~r2_hidden(X18,k1_relat_1(X19)))|(~v1_relat_1(X19)|~v1_funct_1(X19)))&(X18=k1_funct_1(k5_relat_1(X19,k2_funct_1(X19)),X18)|(~v2_funct_1(X19)|~r2_hidden(X18,k1_relat_1(X19)))|(~v1_relat_1(X19)|~v1_funct_1(X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_funct_1])])])).
% 0.19/0.42  cnf(c_0_35, negated_conjecture, (k1_funct_1(esk2_0,k1_funct_1(esk3_0,X1))=X1|~r2_hidden(k1_funct_1(esk3_0,X1),k1_relat_1(esk2_0))|~r2_hidden(X1,k1_relat_1(esk3_0))), inference(er,[status(thm)],[c_0_24])).
% 0.19/0.42  cnf(c_0_36, negated_conjecture, (r2_hidden(k1_funct_1(esk3_0,X1),k1_relat_1(esk2_0))|~r2_hidden(X1,k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])])).
% 0.19/0.42  cnf(c_0_37, plain, (v1_relat_1(k5_relat_1(k4_relat_1(X1),X2))|~v1_relat_1(k5_relat_1(k4_relat_1(X2),X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_21, c_0_29])).
% 0.19/0.42  cnf(c_0_38, plain, (k5_relat_1(k4_relat_1(X1),k6_relat_1(k1_relat_1(X1)))=k4_relat_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_21])).
% 0.19/0.42  cnf(c_0_39, plain, (k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.42  cnf(c_0_40, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.42  cnf(c_0_41, plain, (X1=k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))|~v2_funct_1(X2)|~r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.42  cnf(c_0_42, negated_conjecture, (k1_funct_1(esk2_0,k1_funct_1(esk3_0,X1))=X1|~r2_hidden(X1,k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.42  cnf(c_0_43, negated_conjecture, (v2_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.42  cnf(c_0_44, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.42  cnf(c_0_45, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.42  fof(c_0_46, plain, ![X13]:(~v1_relat_1(X13)|~v1_funct_1(X13)|(~v2_funct_1(X13)|k2_funct_1(X13)=k4_relat_1(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).
% 0.19/0.42  fof(c_0_47, plain, ![X15]:((v1_relat_1(k4_relat_1(X15))|(~v1_relat_1(X15)|~v1_funct_1(X15)|~v2_funct_1(X15)))&(v1_funct_1(k4_relat_1(X15))|(~v1_relat_1(X15)|~v1_funct_1(X15)|~v2_funct_1(X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc5_funct_1])])])).
% 0.19/0.42  cnf(c_0_48, plain, (v1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40])]), c_0_21])).
% 0.19/0.42  cnf(c_0_49, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=k4_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_38]), c_0_39]), c_0_40])])).
% 0.19/0.42  cnf(c_0_50, plain, (k5_relat_1(k4_relat_1(X1),k6_relat_1(X2))=k4_relat_1(k5_relat_1(k6_relat_1(X2),X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_39]), c_0_40])])).
% 0.19/0.42  cnf(c_0_51, plain, (v1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(k4_relat_1(X1))),X1))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_30]), c_0_39]), c_0_40])]), c_0_21])).
% 0.19/0.42  fof(c_0_52, plain, ![X20, X21]:((r2_hidden(esk1_2(X20,X21),k1_relat_1(X20))|k1_relat_1(X20)!=k1_relat_1(X21)|X20=X21|(~v1_relat_1(X21)|~v1_funct_1(X21))|(~v1_relat_1(X20)|~v1_funct_1(X20)))&(k1_funct_1(X20,esk1_2(X20,X21))!=k1_funct_1(X21,esk1_2(X20,X21))|k1_relat_1(X20)!=k1_relat_1(X21)|X20=X21|(~v1_relat_1(X21)|~v1_funct_1(X21))|(~v1_relat_1(X20)|~v1_funct_1(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).
% 0.19/0.42  cnf(c_0_53, negated_conjecture, (k1_funct_1(k2_funct_1(esk2_0),X1)=k1_funct_1(esk3_0,X1)|~r2_hidden(X1,k1_relat_1(esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_44]), c_0_45])]), c_0_36])).
% 0.19/0.42  cnf(c_0_54, plain, (k2_funct_1(X1)=k4_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.42  cnf(c_0_55, negated_conjecture, (k2_relat_1(esk2_0)=k1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.42  cnf(c_0_56, plain, (k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.42  cnf(c_0_57, plain, (v1_funct_1(k4_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.42  cnf(c_0_58, plain, (v1_relat_1(k4_relat_1(k4_relat_1(X1)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.42  cnf(c_0_59, plain, (k4_relat_1(k5_relat_1(k6_relat_1(X1),k4_relat_1(X2)))=k5_relat_1(X2,k6_relat_1(X1))|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_20]), c_0_21])).
% 0.19/0.42  cnf(c_0_60, plain, (v1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(X1)),k4_relat_1(X1)))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_20]), c_0_21])).
% 0.19/0.42  cnf(c_0_61, plain, (r2_hidden(esk1_2(X1,X2),k1_relat_1(X1))|X1=X2|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.42  cnf(c_0_62, negated_conjecture, (esk3_0!=k2_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.42  cnf(c_0_63, plain, (X1=X2|k1_funct_1(X1,esk1_2(X1,X2))!=k1_funct_1(X2,esk1_2(X1,X2))|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.42  cnf(c_0_64, negated_conjecture, (k1_funct_1(k4_relat_1(esk2_0),X1)=k1_funct_1(esk3_0,X1)|~r2_hidden(X1,k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_43]), c_0_44]), c_0_45])])).
% 0.19/0.42  cnf(c_0_65, negated_conjecture, (k1_relat_1(k4_relat_1(esk2_0))=k1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_45])])).
% 0.19/0.42  cnf(c_0_66, negated_conjecture, (v1_funct_1(k4_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_43]), c_0_44]), c_0_45])])).
% 0.19/0.42  cnf(c_0_67, plain, (v1_relat_1(k4_relat_1(k5_relat_1(X1,k6_relat_1(X2))))|~v1_relat_1(k5_relat_1(k6_relat_1(X2),k4_relat_1(X1)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.42  cnf(c_0_68, negated_conjecture, (v1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(esk3_0)),k4_relat_1(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_55]), c_0_45])])).
% 0.19/0.42  cnf(c_0_69, negated_conjecture, (k5_relat_1(esk2_0,k6_relat_1(k1_relat_1(esk3_0)))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_55]), c_0_45])])).
% 0.19/0.42  cnf(c_0_70, negated_conjecture, (X1=esk3_0|r2_hidden(esk1_2(X1,esk3_0),k1_relat_1(X1))|k1_relat_1(X1)!=k1_relat_1(esk3_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_27]), c_0_28])])).
% 0.19/0.42  cnf(c_0_71, negated_conjecture, (k4_relat_1(esk2_0)!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_54]), c_0_43]), c_0_44]), c_0_45])])).
% 0.19/0.42  cnf(c_0_72, negated_conjecture, (k4_relat_1(esk2_0)=X1|k1_funct_1(esk3_0,esk1_2(k4_relat_1(esk2_0),X1))!=k1_funct_1(X1,esk1_2(k4_relat_1(esk2_0),X1))|k1_relat_1(esk3_0)!=k1_relat_1(X1)|~r2_hidden(esk1_2(k4_relat_1(esk2_0),X1),k1_relat_1(esk3_0))|~v1_funct_1(X1)|~v1_relat_1(k4_relat_1(esk2_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), c_0_66])])).
% 0.19/0.42  cnf(c_0_73, negated_conjecture, (v1_relat_1(k4_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69]), c_0_45])])).
% 0.19/0.42  cnf(c_0_74, negated_conjecture, (r2_hidden(esk1_2(k4_relat_1(esk2_0),esk3_0),k1_relat_1(esk3_0))|~v1_relat_1(k4_relat_1(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_65]), c_0_66])]), c_0_71])).
% 0.19/0.42  cnf(c_0_75, negated_conjecture, (k4_relat_1(esk2_0)=X1|k1_funct_1(esk3_0,esk1_2(k4_relat_1(esk2_0),X1))!=k1_funct_1(X1,esk1_2(k4_relat_1(esk2_0),X1))|k1_relat_1(esk3_0)!=k1_relat_1(X1)|~r2_hidden(esk1_2(k4_relat_1(esk2_0),X1),k1_relat_1(esk3_0))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_73])])).
% 0.19/0.42  cnf(c_0_76, negated_conjecture, (r2_hidden(esk1_2(k4_relat_1(esk2_0),esk3_0),k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_73])])).
% 0.19/0.42  cnf(c_0_77, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_27]), c_0_28])]), c_0_71]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 78
% 0.19/0.42  # Proof object clause steps            : 51
% 0.19/0.42  # Proof object formula steps           : 27
% 0.19/0.42  # Proof object conjectures             : 29
% 0.19/0.42  # Proof object clause conjectures      : 26
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 23
% 0.19/0.42  # Proof object initial formulas used   : 13
% 0.19/0.42  # Proof object generating inferences   : 25
% 0.19/0.42  # Proof object simplifying inferences  : 62
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 14
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 28
% 0.19/0.42  # Removed in clause preprocessing      : 0
% 0.19/0.42  # Initial clauses in saturation        : 28
% 0.19/0.42  # Processed clauses                    : 600
% 0.19/0.42  # ...of these trivial                  : 68
% 0.19/0.42  # ...subsumed                          : 277
% 0.19/0.42  # ...remaining for further processing  : 255
% 0.19/0.42  # Other redundant clauses eliminated   : 2
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 7
% 0.19/0.42  # Backward-rewritten                   : 65
% 0.19/0.42  # Generated clauses                    : 1888
% 0.19/0.42  # ...of the previous two non-trivial   : 1516
% 0.19/0.42  # Contextual simplify-reflections      : 32
% 0.19/0.42  # Paramodulations                      : 1882
% 0.19/0.42  # Factorizations                       : 0
% 0.19/0.42  # Equation resolutions                 : 6
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 154
% 0.19/0.42  #    Positive orientable unit clauses  : 32
% 0.19/0.42  #    Positive unorientable unit clauses: 0
% 0.19/0.42  #    Negative unit clauses             : 2
% 0.19/0.42  #    Non-unit-clauses                  : 120
% 0.19/0.42  # Current number of unprocessed clauses: 957
% 0.19/0.42  # ...number of literals in the above   : 4244
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 99
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 4126
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 2671
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 314
% 0.19/0.42  # Unit Clause-clause subsumption calls : 360
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 34
% 0.19/0.42  # BW rewrite match successes           : 9
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 39948
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.073 s
% 0.19/0.42  # System time              : 0.006 s
% 0.19/0.42  # Total time               : 0.079 s
% 0.19/0.42  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
