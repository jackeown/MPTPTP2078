%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:46 EST 2020

% Result     : Theorem 1.08s
% Output     : CNFRefutation 1.08s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 239 expanded)
%              Number of clauses        :   40 (  85 expanded)
%              Number of leaves         :   13 (  60 expanded)
%              Depth                    :   12
%              Number of atoms          :  240 (1053 expanded)
%              Number of equality atoms :   68 ( 316 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(t37_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(involutiveness_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k4_relat_1(k4_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(t160_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(t57_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & r2_hidden(X1,k2_relat_1(X2)) )
       => ( X1 = k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))
          & X1 = k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

fof(t54_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(t56_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & r2_hidden(X1,k1_relat_1(X2)) )
       => ( X1 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))
          & X1 = k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

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

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(c_0_13,plain,(
    ! [X9] :
      ( ~ v1_relat_1(X9)
      | k9_relat_1(X9,k1_relat_1(X9)) = k2_relat_1(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

fof(c_0_14,plain,(
    ! [X12] :
      ( ( k2_relat_1(X12) = k1_relat_1(k4_relat_1(X12))
        | ~ v1_relat_1(X12) )
      & ( k1_relat_1(X12) = k2_relat_1(k4_relat_1(X12))
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

fof(c_0_15,plain,(
    ! [X5] :
      ( ~ v1_relat_1(X5)
      | v1_relat_1(k4_relat_1(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

cnf(c_0_16,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X8] :
      ( ~ v1_relat_1(X8)
      | k4_relat_1(k4_relat_1(X8)) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k4_relat_1])])).

fof(c_0_20,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ v1_relat_1(X11)
      | k2_relat_1(k5_relat_1(X10,X11)) = k9_relat_1(X11,k2_relat_1(X10)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t160_relat_1])])])).

cnf(c_0_21,plain,
    ( k9_relat_1(k4_relat_1(X1),k2_relat_1(X1)) = k2_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_22,plain,
    ( k4_relat_1(k4_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( ( v2_funct_1(X2)
            & r2_hidden(X1,k2_relat_1(X2)) )
         => ( X1 = k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))
            & X1 = k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t57_funct_1])).

cnf(c_0_24,plain,
    ( k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k9_relat_1(X1,k2_relat_1(k4_relat_1(X1))) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_18])).

fof(c_0_26,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ v1_relat_1(X14)
      | k4_relat_1(k5_relat_1(X13,X14)) = k5_relat_1(k4_relat_1(X14),k4_relat_1(X13)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).

fof(c_0_27,plain,(
    ! [X26] :
      ( ~ v1_relat_1(X26)
      | ~ v1_funct_1(X26)
      | ~ v2_funct_1(X26)
      | k2_funct_1(X26) = k4_relat_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

fof(c_0_28,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_funct_1(esk6_0)
    & v2_funct_1(esk6_0)
    & r2_hidden(esk5_0,k2_relat_1(esk6_0))
    & ( esk5_0 != k1_funct_1(esk6_0,k1_funct_1(k2_funct_1(esk6_0),esk5_0))
      | esk5_0 != k1_funct_1(k5_relat_1(k2_funct_1(esk6_0),esk6_0),esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_29,plain,
    ( k2_relat_1(k5_relat_1(k4_relat_1(X1),X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_18])).

cnf(c_0_30,plain,
    ( k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_31,plain,(
    ! [X36,X37] :
      ( ( X36 = k1_funct_1(k2_funct_1(X37),k1_funct_1(X37,X36))
        | ~ v2_funct_1(X37)
        | ~ r2_hidden(X36,k1_relat_1(X37))
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( X36 = k1_funct_1(k5_relat_1(X37,k2_funct_1(X37)),X36)
        | ~ v2_funct_1(X37)
        | ~ r2_hidden(X36,k1_relat_1(X37))
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_funct_1])])])).

cnf(c_0_32,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( v2_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_36,plain,(
    ! [X16,X17,X18,X20,X21,X22,X24] :
      ( ( r2_hidden(esk1_3(X16,X17,X18),k1_relat_1(X16))
        | ~ r2_hidden(X18,X17)
        | X17 != k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( X18 = k1_funct_1(X16,esk1_3(X16,X17,X18))
        | ~ r2_hidden(X18,X17)
        | X17 != k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( ~ r2_hidden(X21,k1_relat_1(X16))
        | X20 != k1_funct_1(X16,X21)
        | r2_hidden(X20,X17)
        | X17 != k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( ~ r2_hidden(esk2_2(X16,X22),X22)
        | ~ r2_hidden(X24,k1_relat_1(X16))
        | esk2_2(X16,X22) != k1_funct_1(X16,X24)
        | X22 = k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( r2_hidden(esk3_2(X16,X22),k1_relat_1(X16))
        | r2_hidden(esk2_2(X16,X22),X22)
        | X22 = k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( esk2_2(X16,X22) = k1_funct_1(X16,esk3_2(X16,X22))
        | r2_hidden(esk2_2(X16,X22),X22)
        | X22 = k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_37,plain,
    ( k2_relat_1(k4_relat_1(k5_relat_1(X1,k4_relat_1(X1)))) = k2_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_18])).

cnf(c_0_38,plain,
    ( X1 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))
    | ~ v2_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( k2_funct_1(esk6_0) = k4_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])])).

cnf(c_0_40,plain,
    ( X1 = k1_funct_1(X2,esk1_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_41,plain,(
    ! [X29,X30,X31] :
      ( ~ v1_relat_1(X30)
      | ~ v1_funct_1(X30)
      | ~ v1_relat_1(X31)
      | ~ v1_funct_1(X31)
      | ~ r2_hidden(X29,k1_relat_1(k5_relat_1(X31,X30)))
      | k1_funct_1(k5_relat_1(X31,X30),X29) = k1_funct_1(X30,k1_funct_1(X31,X29)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).

cnf(c_0_42,plain,
    ( k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_43,plain,
    ( k2_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(X1),X1))) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_22]),c_0_18])).

fof(c_0_44,plain,(
    ! [X27] :
      ( ( v1_relat_1(k2_funct_1(X27))
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( v1_funct_1(k2_funct_1(X27))
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_45,negated_conjecture,
    ( k1_funct_1(k4_relat_1(esk6_0),k1_funct_1(esk6_0,X1)) = X1
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_33]),c_0_34]),c_0_35])])).

cnf(c_0_46,plain,
    ( k1_funct_1(X1,esk1_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( esk5_0 != k1_funct_1(esk6_0,k1_funct_1(k2_funct_1(esk6_0),esk5_0))
    | esk5_0 != k1_funct_1(k5_relat_1(k2_funct_1(esk6_0),esk6_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_49,plain,
    ( k1_funct_1(k5_relat_1(X2,X1),X3) = k1_funct_1(X1,k1_funct_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,plain,
    ( k1_relat_1(k5_relat_1(k4_relat_1(X1),X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(k5_relat_1(k4_relat_1(X1),X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( esk1_3(esk6_0,k2_relat_1(esk6_0),X1) = k1_funct_1(k4_relat_1(esk6_0),X1)
    | ~ r2_hidden(esk1_3(esk6_0,k2_relat_1(esk6_0),X1),k1_relat_1(esk6_0))
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_34]),c_0_35])])).

cnf(c_0_53,plain,
    ( r2_hidden(esk1_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( k1_funct_1(esk6_0,k1_funct_1(k4_relat_1(esk6_0),esk5_0)) != esk5_0
    | k1_funct_1(k5_relat_1(k4_relat_1(esk6_0),esk6_0),esk5_0) != esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_39]),c_0_39])).

cnf(c_0_55,plain,
    ( k1_funct_1(k5_relat_1(k4_relat_1(X1),X1),X2) = k1_funct_1(X1,k1_funct_1(k4_relat_1(X1),X2))
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(k4_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k5_relat_1(k4_relat_1(X1),X1))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_18])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk5_0,k2_relat_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_1(k4_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_39]),c_0_34]),c_0_35])])).

cnf(c_0_58,negated_conjecture,
    ( esk1_3(esk6_0,k2_relat_1(esk6_0),X1) = k1_funct_1(k4_relat_1(esk6_0),X1)
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_34]),c_0_35])])).

cnf(c_0_59,negated_conjecture,
    ( k1_funct_1(esk6_0,k1_funct_1(k4_relat_1(esk6_0),esk5_0)) != esk5_0
    | ~ v1_relat_1(k5_relat_1(k4_relat_1(esk6_0),esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_57]),c_0_34]),c_0_35])])).

cnf(c_0_60,negated_conjecture,
    ( k1_funct_1(esk6_0,k1_funct_1(k4_relat_1(esk6_0),X1)) = X1
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_58]),c_0_34]),c_0_35])])).

fof(c_0_61,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X6)
      | ~ v1_relat_1(X7)
      | v1_relat_1(k5_relat_1(X6,X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_62,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_relat_1(k5_relat_1(k4_relat_1(esk6_0),esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_56])])).

cnf(c_0_64,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( v1_relat_1(k4_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_39]),c_0_34]),c_0_35])])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_35]),c_0_65])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:52:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.08/1.25  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.08/1.25  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.08/1.25  #
% 1.08/1.25  # Preprocessing time       : 0.028 s
% 1.08/1.25  # Presaturation interreduction done
% 1.08/1.25  
% 1.08/1.25  # Proof found!
% 1.08/1.25  # SZS status Theorem
% 1.08/1.25  # SZS output start CNFRefutation
% 1.08/1.25  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 1.08/1.25  fof(t37_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))&k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 1.08/1.25  fof(dt_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>v1_relat_1(k4_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 1.08/1.25  fof(involutiveness_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k4_relat_1(k4_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 1.08/1.25  fof(t160_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k2_relat_1(k5_relat_1(X1,X2))=k9_relat_1(X2,k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 1.08/1.25  fof(t57_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k2_relat_1(X2)))=>(X1=k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))&X1=k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_funct_1)).
% 1.08/1.25  fof(t54_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 1.08/1.25  fof(d9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(X1)=k4_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 1.08/1.25  fof(t56_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k1_relat_1(X2)))=>(X1=k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))&X1=k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 1.08/1.25  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 1.08/1.25  fof(t22_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))=>k1_funct_1(k5_relat_1(X3,X2),X1)=k1_funct_1(X2,k1_funct_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 1.08/1.25  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 1.08/1.25  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 1.08/1.25  fof(c_0_13, plain, ![X9]:(~v1_relat_1(X9)|k9_relat_1(X9,k1_relat_1(X9))=k2_relat_1(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 1.08/1.25  fof(c_0_14, plain, ![X12]:((k2_relat_1(X12)=k1_relat_1(k4_relat_1(X12))|~v1_relat_1(X12))&(k1_relat_1(X12)=k2_relat_1(k4_relat_1(X12))|~v1_relat_1(X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).
% 1.08/1.25  fof(c_0_15, plain, ![X5]:(~v1_relat_1(X5)|v1_relat_1(k4_relat_1(X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).
% 1.08/1.25  cnf(c_0_16, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.08/1.25  cnf(c_0_17, plain, (k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.08/1.25  cnf(c_0_18, plain, (v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.08/1.25  fof(c_0_19, plain, ![X8]:(~v1_relat_1(X8)|k4_relat_1(k4_relat_1(X8))=X8), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k4_relat_1])])).
% 1.08/1.25  fof(c_0_20, plain, ![X10, X11]:(~v1_relat_1(X10)|(~v1_relat_1(X11)|k2_relat_1(k5_relat_1(X10,X11))=k9_relat_1(X11,k2_relat_1(X10)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t160_relat_1])])])).
% 1.08/1.25  cnf(c_0_21, plain, (k9_relat_1(k4_relat_1(X1),k2_relat_1(X1))=k2_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 1.08/1.25  cnf(c_0_22, plain, (k4_relat_1(k4_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.08/1.25  fof(c_0_23, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k2_relat_1(X2)))=>(X1=k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))&X1=k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1))))), inference(assume_negation,[status(cth)],[t57_funct_1])).
% 1.08/1.25  cnf(c_0_24, plain, (k2_relat_1(k5_relat_1(X1,X2))=k9_relat_1(X2,k2_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.08/1.25  cnf(c_0_25, plain, (k9_relat_1(X1,k2_relat_1(k4_relat_1(X1)))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_18])).
% 1.08/1.25  fof(c_0_26, plain, ![X13, X14]:(~v1_relat_1(X13)|(~v1_relat_1(X14)|k4_relat_1(k5_relat_1(X13,X14))=k5_relat_1(k4_relat_1(X14),k4_relat_1(X13)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).
% 1.08/1.25  fof(c_0_27, plain, ![X26]:(~v1_relat_1(X26)|~v1_funct_1(X26)|(~v2_funct_1(X26)|k2_funct_1(X26)=k4_relat_1(X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).
% 1.08/1.25  fof(c_0_28, negated_conjecture, ((v1_relat_1(esk6_0)&v1_funct_1(esk6_0))&((v2_funct_1(esk6_0)&r2_hidden(esk5_0,k2_relat_1(esk6_0)))&(esk5_0!=k1_funct_1(esk6_0,k1_funct_1(k2_funct_1(esk6_0),esk5_0))|esk5_0!=k1_funct_1(k5_relat_1(k2_funct_1(esk6_0),esk6_0),esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 1.08/1.25  cnf(c_0_29, plain, (k2_relat_1(k5_relat_1(k4_relat_1(X1),X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_18])).
% 1.08/1.25  cnf(c_0_30, plain, (k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.08/1.25  fof(c_0_31, plain, ![X36, X37]:((X36=k1_funct_1(k2_funct_1(X37),k1_funct_1(X37,X36))|(~v2_funct_1(X37)|~r2_hidden(X36,k1_relat_1(X37)))|(~v1_relat_1(X37)|~v1_funct_1(X37)))&(X36=k1_funct_1(k5_relat_1(X37,k2_funct_1(X37)),X36)|(~v2_funct_1(X37)|~r2_hidden(X36,k1_relat_1(X37)))|(~v1_relat_1(X37)|~v1_funct_1(X37)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_funct_1])])])).
% 1.08/1.25  cnf(c_0_32, plain, (k2_funct_1(X1)=k4_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.08/1.25  cnf(c_0_33, negated_conjecture, (v2_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.08/1.25  cnf(c_0_34, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.08/1.25  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.08/1.25  fof(c_0_36, plain, ![X16, X17, X18, X20, X21, X22, X24]:((((r2_hidden(esk1_3(X16,X17,X18),k1_relat_1(X16))|~r2_hidden(X18,X17)|X17!=k2_relat_1(X16)|(~v1_relat_1(X16)|~v1_funct_1(X16)))&(X18=k1_funct_1(X16,esk1_3(X16,X17,X18))|~r2_hidden(X18,X17)|X17!=k2_relat_1(X16)|(~v1_relat_1(X16)|~v1_funct_1(X16))))&(~r2_hidden(X21,k1_relat_1(X16))|X20!=k1_funct_1(X16,X21)|r2_hidden(X20,X17)|X17!=k2_relat_1(X16)|(~v1_relat_1(X16)|~v1_funct_1(X16))))&((~r2_hidden(esk2_2(X16,X22),X22)|(~r2_hidden(X24,k1_relat_1(X16))|esk2_2(X16,X22)!=k1_funct_1(X16,X24))|X22=k2_relat_1(X16)|(~v1_relat_1(X16)|~v1_funct_1(X16)))&((r2_hidden(esk3_2(X16,X22),k1_relat_1(X16))|r2_hidden(esk2_2(X16,X22),X22)|X22=k2_relat_1(X16)|(~v1_relat_1(X16)|~v1_funct_1(X16)))&(esk2_2(X16,X22)=k1_funct_1(X16,esk3_2(X16,X22))|r2_hidden(esk2_2(X16,X22),X22)|X22=k2_relat_1(X16)|(~v1_relat_1(X16)|~v1_funct_1(X16)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 1.08/1.25  cnf(c_0_37, plain, (k2_relat_1(k4_relat_1(k5_relat_1(X1,k4_relat_1(X1))))=k2_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_18])).
% 1.08/1.25  cnf(c_0_38, plain, (X1=k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))|~v2_funct_1(X2)|~r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.08/1.25  cnf(c_0_39, negated_conjecture, (k2_funct_1(esk6_0)=k4_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35])])).
% 1.08/1.25  cnf(c_0_40, plain, (X1=k1_funct_1(X2,esk1_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.08/1.25  fof(c_0_41, plain, ![X29, X30, X31]:(~v1_relat_1(X30)|~v1_funct_1(X30)|(~v1_relat_1(X31)|~v1_funct_1(X31)|(~r2_hidden(X29,k1_relat_1(k5_relat_1(X31,X30)))|k1_funct_1(k5_relat_1(X31,X30),X29)=k1_funct_1(X30,k1_funct_1(X31,X29))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).
% 1.08/1.25  cnf(c_0_42, plain, (k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.08/1.25  cnf(c_0_43, plain, (k2_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(X1),X1)))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_22]), c_0_18])).
% 1.08/1.25  fof(c_0_44, plain, ![X27]:((v1_relat_1(k2_funct_1(X27))|(~v1_relat_1(X27)|~v1_funct_1(X27)))&(v1_funct_1(k2_funct_1(X27))|(~v1_relat_1(X27)|~v1_funct_1(X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 1.08/1.25  cnf(c_0_45, negated_conjecture, (k1_funct_1(k4_relat_1(esk6_0),k1_funct_1(esk6_0,X1))=X1|~r2_hidden(X1,k1_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_33]), c_0_34]), c_0_35])])).
% 1.08/1.25  cnf(c_0_46, plain, (k1_funct_1(X1,esk1_3(X1,k2_relat_1(X1),X2))=X2|~r2_hidden(X2,k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_40])).
% 1.08/1.25  cnf(c_0_47, plain, (r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.08/1.25  cnf(c_0_48, negated_conjecture, (esk5_0!=k1_funct_1(esk6_0,k1_funct_1(k2_funct_1(esk6_0),esk5_0))|esk5_0!=k1_funct_1(k5_relat_1(k2_funct_1(esk6_0),esk6_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.08/1.25  cnf(c_0_49, plain, (k1_funct_1(k5_relat_1(X2,X1),X3)=k1_funct_1(X1,k1_funct_1(X2,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.08/1.25  cnf(c_0_50, plain, (k1_relat_1(k5_relat_1(k4_relat_1(X1),X1))=k2_relat_1(X1)|~v1_relat_1(k5_relat_1(k4_relat_1(X1),X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 1.08/1.25  cnf(c_0_51, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.08/1.25  cnf(c_0_52, negated_conjecture, (esk1_3(esk6_0,k2_relat_1(esk6_0),X1)=k1_funct_1(k4_relat_1(esk6_0),X1)|~r2_hidden(esk1_3(esk6_0,k2_relat_1(esk6_0),X1),k1_relat_1(esk6_0))|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_34]), c_0_35])])).
% 1.08/1.25  cnf(c_0_53, plain, (r2_hidden(esk1_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~r2_hidden(X2,k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_47])).
% 1.08/1.25  cnf(c_0_54, negated_conjecture, (k1_funct_1(esk6_0,k1_funct_1(k4_relat_1(esk6_0),esk5_0))!=esk5_0|k1_funct_1(k5_relat_1(k4_relat_1(esk6_0),esk6_0),esk5_0)!=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_39]), c_0_39])).
% 1.08/1.25  cnf(c_0_55, plain, (k1_funct_1(k5_relat_1(k4_relat_1(X1),X1),X2)=k1_funct_1(X1,k1_funct_1(k4_relat_1(X1),X2))|~r2_hidden(X2,k2_relat_1(X1))|~v1_funct_1(k4_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k5_relat_1(k4_relat_1(X1),X1))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_18])).
% 1.08/1.25  cnf(c_0_56, negated_conjecture, (r2_hidden(esk5_0,k2_relat_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.08/1.25  cnf(c_0_57, negated_conjecture, (v1_funct_1(k4_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_39]), c_0_34]), c_0_35])])).
% 1.08/1.25  cnf(c_0_58, negated_conjecture, (esk1_3(esk6_0,k2_relat_1(esk6_0),X1)=k1_funct_1(k4_relat_1(esk6_0),X1)|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_34]), c_0_35])])).
% 1.08/1.25  cnf(c_0_59, negated_conjecture, (k1_funct_1(esk6_0,k1_funct_1(k4_relat_1(esk6_0),esk5_0))!=esk5_0|~v1_relat_1(k5_relat_1(k4_relat_1(esk6_0),esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_57]), c_0_34]), c_0_35])])).
% 1.08/1.25  cnf(c_0_60, negated_conjecture, (k1_funct_1(esk6_0,k1_funct_1(k4_relat_1(esk6_0),X1))=X1|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_58]), c_0_34]), c_0_35])])).
% 1.08/1.25  fof(c_0_61, plain, ![X6, X7]:(~v1_relat_1(X6)|~v1_relat_1(X7)|v1_relat_1(k5_relat_1(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 1.08/1.25  cnf(c_0_62, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.08/1.25  cnf(c_0_63, negated_conjecture, (~v1_relat_1(k5_relat_1(k4_relat_1(esk6_0),esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_56])])).
% 1.08/1.25  cnf(c_0_64, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 1.08/1.25  cnf(c_0_65, negated_conjecture, (v1_relat_1(k4_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_39]), c_0_34]), c_0_35])])).
% 1.08/1.25  cnf(c_0_66, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_35]), c_0_65])]), ['proof']).
% 1.08/1.25  # SZS output end CNFRefutation
% 1.08/1.25  # Proof object total steps             : 67
% 1.08/1.25  # Proof object clause steps            : 40
% 1.08/1.25  # Proof object formula steps           : 27
% 1.08/1.25  # Proof object conjectures             : 19
% 1.08/1.25  # Proof object clause conjectures      : 16
% 1.08/1.25  # Proof object formula conjectures     : 3
% 1.08/1.25  # Proof object initial clauses used    : 20
% 1.08/1.25  # Proof object initial formulas used   : 13
% 1.08/1.25  # Proof object generating inferences   : 17
% 1.08/1.25  # Proof object simplifying inferences  : 42
% 1.08/1.25  # Training examples: 0 positive, 0 negative
% 1.08/1.25  # Parsed axioms                        : 16
% 1.08/1.25  # Removed by relevancy pruning/SinE    : 0
% 1.08/1.25  # Initial clauses                      : 32
% 1.08/1.25  # Removed in clause preprocessing      : 0
% 1.08/1.25  # Initial clauses in saturation        : 32
% 1.08/1.25  # Processed clauses                    : 6334
% 1.08/1.25  # ...of these trivial                  : 10
% 1.08/1.25  # ...subsumed                          : 5322
% 1.08/1.25  # ...remaining for further processing  : 1002
% 1.08/1.25  # Other redundant clauses eliminated   : 25
% 1.08/1.25  # Clauses deleted for lack of memory   : 0
% 1.08/1.25  # Backward-subsumed                    : 37
% 1.08/1.25  # Backward-rewritten                   : 25
% 1.08/1.25  # Generated clauses                    : 73042
% 1.08/1.25  # ...of the previous two non-trivial   : 69753
% 1.08/1.25  # Contextual simplify-reflections      : 393
% 1.08/1.25  # Paramodulations                      : 73016
% 1.08/1.25  # Factorizations                       : 2
% 1.08/1.25  # Equation resolutions                 : 25
% 1.08/1.25  # Propositional unsat checks           : 0
% 1.08/1.25  #    Propositional check models        : 0
% 1.08/1.25  #    Propositional check unsatisfiable : 0
% 1.08/1.25  #    Propositional clauses             : 0
% 1.08/1.25  #    Propositional clauses after purity: 0
% 1.08/1.25  #    Propositional unsat core size     : 0
% 1.08/1.25  #    Propositional preprocessing time  : 0.000
% 1.08/1.25  #    Propositional encoding time       : 0.000
% 1.08/1.25  #    Propositional solver time         : 0.000
% 1.08/1.25  #    Success case prop preproc time    : 0.000
% 1.08/1.25  #    Success case prop encoding time   : 0.000
% 1.08/1.25  #    Success case prop solver time     : 0.000
% 1.08/1.25  # Current number of processed clauses  : 901
% 1.08/1.25  #    Positive orientable unit clauses  : 24
% 1.08/1.25  #    Positive unorientable unit clauses: 0
% 1.08/1.25  #    Negative unit clauses             : 1
% 1.08/1.25  #    Non-unit-clauses                  : 876
% 1.08/1.25  # Current number of unprocessed clauses: 63327
% 1.08/1.25  # ...number of literals in the above   : 322763
% 1.08/1.25  # Current number of archived formulas  : 0
% 1.08/1.25  # Current number of archived clauses   : 94
% 1.08/1.25  # Clause-clause subsumption calls (NU) : 306130
% 1.08/1.25  # Rec. Clause-clause subsumption calls : 154818
% 1.08/1.25  # Non-unit clause-clause subsumptions  : 5752
% 1.08/1.25  # Unit Clause-clause subsumption calls : 1154
% 1.08/1.25  # Rewrite failures with RHS unbound    : 0
% 1.08/1.25  # BW rewrite match attempts            : 95
% 1.08/1.25  # BW rewrite match successes           : 12
% 1.08/1.25  # Condensation attempts                : 0
% 1.08/1.25  # Condensation successes               : 0
% 1.08/1.25  # Termbank termtop insertions          : 2470418
% 1.08/1.26  
% 1.08/1.26  # -------------------------------------------------
% 1.08/1.26  # User time                : 0.876 s
% 1.08/1.26  # System time              : 0.038 s
% 1.08/1.26  # Total time               : 0.914 s
% 1.08/1.26  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
