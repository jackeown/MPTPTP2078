%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:47 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 292 expanded)
%              Number of clauses        :   40 ( 102 expanded)
%              Number of leaves         :   14 (  73 expanded)
%              Depth                    :   10
%              Number of atoms          :  230 (1256 expanded)
%              Number of equality atoms :   67 ( 384 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

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

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

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

fof(t20_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k2_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

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

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( ( v2_funct_1(X2)
            & r2_hidden(X1,k2_relat_1(X2)) )
         => ( X1 = k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))
            & X1 = k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t57_funct_1])).

fof(c_0_15,plain,(
    ! [X25] :
      ( ~ v1_relat_1(X25)
      | ~ v1_funct_1(X25)
      | ~ v2_funct_1(X25)
      | k2_funct_1(X25) = k4_relat_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

fof(c_0_16,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & v2_funct_1(esk5_0)
    & r2_hidden(esk4_0,k2_relat_1(esk5_0))
    & ( esk4_0 != k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))
      | esk4_0 != k1_funct_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0),esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_17,plain,(
    ! [X31,X32] :
      ( ( X31 = k1_funct_1(k2_funct_1(X32),k1_funct_1(X32,X31))
        | ~ v2_funct_1(X32)
        | ~ r2_hidden(X31,k1_relat_1(X32))
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( X31 = k1_funct_1(k5_relat_1(X32,k2_funct_1(X32)),X31)
        | ~ v2_funct_1(X32)
        | ~ r2_hidden(X31,k1_relat_1(X32))
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_funct_1])])])).

cnf(c_0_18,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X33,X34,X35] :
      ( ( r2_hidden(X33,k1_relat_1(X35))
        | ~ r2_hidden(k4_tarski(X33,X34),X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( X34 = k1_funct_1(X35,X33)
        | ~ r2_hidden(k4_tarski(X33,X34),X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( ~ r2_hidden(X33,k1_relat_1(X35))
        | X34 != k1_funct_1(X35,X33)
        | r2_hidden(k4_tarski(X33,X34),X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_23,plain,(
    ! [X5,X6,X7,X9,X10,X11,X12,X14] :
      ( ( ~ r2_hidden(X7,X6)
        | r2_hidden(k4_tarski(esk1_3(X5,X6,X7),X7),X5)
        | X6 != k2_relat_1(X5) )
      & ( ~ r2_hidden(k4_tarski(X10,X9),X5)
        | r2_hidden(X9,X6)
        | X6 != k2_relat_1(X5) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | ~ r2_hidden(k4_tarski(X14,esk2_2(X11,X12)),X11)
        | X12 = k2_relat_1(X11) )
      & ( r2_hidden(esk2_2(X11,X12),X12)
        | r2_hidden(k4_tarski(esk3_2(X11,X12),esk2_2(X11,X12)),X11)
        | X12 = k2_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_24,plain,(
    ! [X22] :
      ( ( k2_relat_1(X22) = k1_relat_1(k4_relat_1(X22))
        | ~ v1_relat_1(X22) )
      & ( k1_relat_1(X22) = k2_relat_1(k4_relat_1(X22))
        | ~ v1_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

fof(c_0_25,plain,(
    ! [X16] :
      ( ~ v1_relat_1(X16)
      | v1_relat_1(k4_relat_1(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

cnf(c_0_26,plain,
    ( X1 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))
    | ~ v2_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( k2_funct_1(esk5_0) = k4_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_28,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(esk1_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X19,X20,X21] :
      ( ( r2_hidden(X19,k1_relat_1(X21))
        | ~ r2_hidden(k4_tarski(X19,X20),X21)
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(X20,k2_relat_1(X21))
        | ~ r2_hidden(k4_tarski(X19,X20),X21)
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).

fof(c_0_31,plain,(
    ! [X24] :
      ( ~ v1_relat_1(X24)
      | k5_relat_1(X24,k6_relat_1(k2_relat_1(X24))) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

cnf(c_0_32,plain,
    ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_35,plain,(
    ! [X26] :
      ( ( v1_relat_1(k2_funct_1(X26))
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( v1_funct_1(k2_funct_1(X26))
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_36,negated_conjecture,
    ( k1_funct_1(k4_relat_1(esk5_0),k1_funct_1(esk5_0,X1)) = X1
    | ~ r2_hidden(X1,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_37,plain,
    ( k1_funct_1(X1,esk1_3(X1,X2,X3)) = X3
    | X2 != k2_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( k1_relat_1(k4_relat_1(k4_relat_1(X1))) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_41,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( esk1_3(esk5_0,X1,X2) = k1_funct_1(k4_relat_1(esk5_0),X2)
    | X1 != k2_relat_1(esk5_0)
    | ~ r2_hidden(esk1_3(esk5_0,X1,X2),k1_relat_1(esk5_0))
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_20]),c_0_21])])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X1))
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_29])).

fof(c_0_44,plain,(
    ! [X28,X29,X30] :
      ( ~ v1_relat_1(X29)
      | ~ v1_funct_1(X29)
      | ~ v1_relat_1(X30)
      | ~ v1_funct_1(X30)
      | ~ r2_hidden(X28,k1_relat_1(k5_relat_1(X30,X29)))
      | k1_funct_1(k5_relat_1(X30,X29),X28) = k1_funct_1(X29,k1_funct_1(X30,X28)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).

fof(c_0_45,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X17)
      | ~ v1_relat_1(X18)
      | k1_relat_1(k5_relat_1(X17,X18)) = k10_relat_1(X17,k1_relat_1(X18)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

cnf(c_0_46,plain,
    ( k5_relat_1(X1,k6_relat_1(k1_relat_1(k4_relat_1(X1)))) = X1
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_32])).

cnf(c_0_47,negated_conjecture,
    ( k1_relat_1(k4_relat_1(k4_relat_1(esk5_0))) = k1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_21])).

cnf(c_0_48,negated_conjecture,
    ( v1_relat_1(k4_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_27]),c_0_20]),c_0_21])])).

fof(c_0_49,plain,(
    ! [X23] :
      ( k1_relat_1(k6_relat_1(X23)) = X23
      & k2_relat_1(k6_relat_1(X23)) = X23 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_50,plain,(
    ! [X27] :
      ( v1_relat_1(k6_relat_1(X27))
      & v2_funct_1(k6_relat_1(X27)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

cnf(c_0_51,negated_conjecture,
    ( esk1_3(esk5_0,X1,X2) = k1_funct_1(k4_relat_1(esk5_0),X2)
    | X1 != k2_relat_1(esk5_0)
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_21])])).

cnf(c_0_52,negated_conjecture,
    ( esk4_0 != k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))
    | esk4_0 != k1_funct_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_53,plain,
    ( k1_funct_1(k5_relat_1(X2,X1),X3) = k1_funct_1(X1,k1_funct_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_56,negated_conjecture,
    ( k5_relat_1(k4_relat_1(esk5_0),k6_relat_1(k1_relat_1(esk5_0))) = k4_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])])).

cnf(c_0_57,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_58,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk4_0,k2_relat_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_60,negated_conjecture,
    ( k1_funct_1(esk5_0,k1_funct_1(k4_relat_1(esk5_0),X1)) = X1
    | X2 != k2_relat_1(esk5_0)
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_51]),c_0_20]),c_0_21])])).

cnf(c_0_61,negated_conjecture,
    ( k1_funct_1(esk5_0,k1_funct_1(k4_relat_1(esk5_0),esk4_0)) != esk4_0
    | k1_funct_1(k5_relat_1(k4_relat_1(esk5_0),esk5_0),esk4_0) != esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_27]),c_0_27])).

cnf(c_0_62,plain,
    ( k1_funct_1(k5_relat_1(X1,X2),X3) = k1_funct_1(X2,k1_funct_1(X1,X3))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X3,k10_relat_1(X1,k1_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( v1_funct_1(k4_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_27]),c_0_20]),c_0_21])])).

cnf(c_0_64,negated_conjecture,
    ( k10_relat_1(k4_relat_1(esk5_0),k1_relat_1(esk5_0)) = k1_relat_1(k4_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_56]),c_0_57]),c_0_58]),c_0_48])])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk4_0,k1_relat_1(k4_relat_1(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_32]),c_0_21])])).

cnf(c_0_66,negated_conjecture,
    ( k1_funct_1(esk5_0,k1_funct_1(k4_relat_1(esk5_0),X1)) = X1
    | ~ r2_hidden(X1,k2_relat_1(esk5_0)) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( k1_funct_1(esk5_0,k1_funct_1(k4_relat_1(esk5_0),esk4_0)) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_20]),c_0_48]),c_0_21]),c_0_64]),c_0_65])])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_59]),c_0_67]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:15:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 0.20/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.028 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t57_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k2_relat_1(X2)))=>(X1=k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))&X1=k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_funct_1)).
% 0.20/0.41  fof(d9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(X1)=k4_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 0.20/0.41  fof(t56_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k1_relat_1(X2)))=>(X1=k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))&X1=k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 0.20/0.41  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 0.20/0.41  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.20/0.41  fof(t37_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))&k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 0.20/0.41  fof(dt_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>v1_relat_1(k4_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 0.20/0.41  fof(t20_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k2_relat_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 0.20/0.41  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 0.20/0.41  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.20/0.41  fof(t22_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))=>k1_funct_1(k5_relat_1(X3,X2),X1)=k1_funct_1(X2,k1_funct_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 0.20/0.41  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 0.20/0.41  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.20/0.41  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.20/0.41  fof(c_0_14, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k2_relat_1(X2)))=>(X1=k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))&X1=k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1))))), inference(assume_negation,[status(cth)],[t57_funct_1])).
% 0.20/0.41  fof(c_0_15, plain, ![X25]:(~v1_relat_1(X25)|~v1_funct_1(X25)|(~v2_funct_1(X25)|k2_funct_1(X25)=k4_relat_1(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).
% 0.20/0.41  fof(c_0_16, negated_conjecture, ((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&((v2_funct_1(esk5_0)&r2_hidden(esk4_0,k2_relat_1(esk5_0)))&(esk4_0!=k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))|esk4_0!=k1_funct_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0),esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.20/0.41  fof(c_0_17, plain, ![X31, X32]:((X31=k1_funct_1(k2_funct_1(X32),k1_funct_1(X32,X31))|(~v2_funct_1(X32)|~r2_hidden(X31,k1_relat_1(X32)))|(~v1_relat_1(X32)|~v1_funct_1(X32)))&(X31=k1_funct_1(k5_relat_1(X32,k2_funct_1(X32)),X31)|(~v2_funct_1(X32)|~r2_hidden(X31,k1_relat_1(X32)))|(~v1_relat_1(X32)|~v1_funct_1(X32)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_funct_1])])])).
% 0.20/0.41  cnf(c_0_18, plain, (k2_funct_1(X1)=k4_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_19, negated_conjecture, (v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_20, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  fof(c_0_22, plain, ![X33, X34, X35]:(((r2_hidden(X33,k1_relat_1(X35))|~r2_hidden(k4_tarski(X33,X34),X35)|(~v1_relat_1(X35)|~v1_funct_1(X35)))&(X34=k1_funct_1(X35,X33)|~r2_hidden(k4_tarski(X33,X34),X35)|(~v1_relat_1(X35)|~v1_funct_1(X35))))&(~r2_hidden(X33,k1_relat_1(X35))|X34!=k1_funct_1(X35,X33)|r2_hidden(k4_tarski(X33,X34),X35)|(~v1_relat_1(X35)|~v1_funct_1(X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.20/0.41  fof(c_0_23, plain, ![X5, X6, X7, X9, X10, X11, X12, X14]:(((~r2_hidden(X7,X6)|r2_hidden(k4_tarski(esk1_3(X5,X6,X7),X7),X5)|X6!=k2_relat_1(X5))&(~r2_hidden(k4_tarski(X10,X9),X5)|r2_hidden(X9,X6)|X6!=k2_relat_1(X5)))&((~r2_hidden(esk2_2(X11,X12),X12)|~r2_hidden(k4_tarski(X14,esk2_2(X11,X12)),X11)|X12=k2_relat_1(X11))&(r2_hidden(esk2_2(X11,X12),X12)|r2_hidden(k4_tarski(esk3_2(X11,X12),esk2_2(X11,X12)),X11)|X12=k2_relat_1(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.20/0.41  fof(c_0_24, plain, ![X22]:((k2_relat_1(X22)=k1_relat_1(k4_relat_1(X22))|~v1_relat_1(X22))&(k1_relat_1(X22)=k2_relat_1(k4_relat_1(X22))|~v1_relat_1(X22))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).
% 0.20/0.41  fof(c_0_25, plain, ![X16]:(~v1_relat_1(X16)|v1_relat_1(k4_relat_1(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).
% 0.20/0.41  cnf(c_0_26, plain, (X1=k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))|~v2_funct_1(X2)|~r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.41  cnf(c_0_27, negated_conjecture, (k2_funct_1(esk5_0)=k4_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21])])).
% 0.20/0.41  cnf(c_0_28, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.41  cnf(c_0_29, plain, (r2_hidden(k4_tarski(esk1_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.41  fof(c_0_30, plain, ![X19, X20, X21]:((r2_hidden(X19,k1_relat_1(X21))|~r2_hidden(k4_tarski(X19,X20),X21)|~v1_relat_1(X21))&(r2_hidden(X20,k2_relat_1(X21))|~r2_hidden(k4_tarski(X19,X20),X21)|~v1_relat_1(X21))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).
% 0.20/0.41  fof(c_0_31, plain, ![X24]:(~v1_relat_1(X24)|k5_relat_1(X24,k6_relat_1(k2_relat_1(X24)))=X24), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 0.20/0.41  cnf(c_0_32, plain, (k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.41  cnf(c_0_33, plain, (k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.41  cnf(c_0_34, plain, (v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.41  fof(c_0_35, plain, ![X26]:((v1_relat_1(k2_funct_1(X26))|(~v1_relat_1(X26)|~v1_funct_1(X26)))&(v1_funct_1(k2_funct_1(X26))|(~v1_relat_1(X26)|~v1_funct_1(X26)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.20/0.41  cnf(c_0_36, negated_conjecture, (k1_funct_1(k4_relat_1(esk5_0),k1_funct_1(esk5_0,X1))=X1|~r2_hidden(X1,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_19]), c_0_20]), c_0_21])])).
% 0.20/0.41  cnf(c_0_37, plain, (k1_funct_1(X1,esk1_3(X1,X2,X3))=X3|X2!=k2_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.41  cnf(c_0_38, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.41  cnf(c_0_39, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.41  cnf(c_0_40, plain, (k1_relat_1(k4_relat_1(k4_relat_1(X1)))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.20/0.41  cnf(c_0_41, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.41  cnf(c_0_42, negated_conjecture, (esk1_3(esk5_0,X1,X2)=k1_funct_1(k4_relat_1(esk5_0),X2)|X1!=k2_relat_1(esk5_0)|~r2_hidden(esk1_3(esk5_0,X1,X2),k1_relat_1(esk5_0))|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_20]), c_0_21])])).
% 0.20/0.41  cnf(c_0_43, plain, (r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X1))|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_38, c_0_29])).
% 0.20/0.41  fof(c_0_44, plain, ![X28, X29, X30]:(~v1_relat_1(X29)|~v1_funct_1(X29)|(~v1_relat_1(X30)|~v1_funct_1(X30)|(~r2_hidden(X28,k1_relat_1(k5_relat_1(X30,X29)))|k1_funct_1(k5_relat_1(X30,X29),X28)=k1_funct_1(X29,k1_funct_1(X30,X28))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).
% 0.20/0.41  fof(c_0_45, plain, ![X17, X18]:(~v1_relat_1(X17)|(~v1_relat_1(X18)|k1_relat_1(k5_relat_1(X17,X18))=k10_relat_1(X17,k1_relat_1(X18)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.20/0.41  cnf(c_0_46, plain, (k5_relat_1(X1,k6_relat_1(k1_relat_1(k4_relat_1(X1))))=X1|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_39, c_0_32])).
% 0.20/0.41  cnf(c_0_47, negated_conjecture, (k1_relat_1(k4_relat_1(k4_relat_1(esk5_0)))=k1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_40, c_0_21])).
% 0.20/0.41  cnf(c_0_48, negated_conjecture, (v1_relat_1(k4_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_27]), c_0_20]), c_0_21])])).
% 0.20/0.41  fof(c_0_49, plain, ![X23]:(k1_relat_1(k6_relat_1(X23))=X23&k2_relat_1(k6_relat_1(X23))=X23), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.20/0.41  fof(c_0_50, plain, ![X27]:(v1_relat_1(k6_relat_1(X27))&v2_funct_1(k6_relat_1(X27))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.20/0.41  cnf(c_0_51, negated_conjecture, (esk1_3(esk5_0,X1,X2)=k1_funct_1(k4_relat_1(esk5_0),X2)|X1!=k2_relat_1(esk5_0)|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_21])])).
% 0.20/0.41  cnf(c_0_52, negated_conjecture, (esk4_0!=k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))|esk4_0!=k1_funct_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_53, plain, (k1_funct_1(k5_relat_1(X2,X1),X3)=k1_funct_1(X1,k1_funct_1(X2,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.41  cnf(c_0_54, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.41  cnf(c_0_55, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.41  cnf(c_0_56, negated_conjecture, (k5_relat_1(k4_relat_1(esk5_0),k6_relat_1(k1_relat_1(esk5_0)))=k4_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])])).
% 0.20/0.41  cnf(c_0_57, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.41  cnf(c_0_58, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.41  cnf(c_0_59, negated_conjecture, (r2_hidden(esk4_0,k2_relat_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_60, negated_conjecture, (k1_funct_1(esk5_0,k1_funct_1(k4_relat_1(esk5_0),X1))=X1|X2!=k2_relat_1(esk5_0)|~r2_hidden(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_51]), c_0_20]), c_0_21])])).
% 0.20/0.41  cnf(c_0_61, negated_conjecture, (k1_funct_1(esk5_0,k1_funct_1(k4_relat_1(esk5_0),esk4_0))!=esk4_0|k1_funct_1(k5_relat_1(k4_relat_1(esk5_0),esk5_0),esk4_0)!=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_27]), c_0_27])).
% 0.20/0.41  cnf(c_0_62, plain, (k1_funct_1(k5_relat_1(X1,X2),X3)=k1_funct_1(X2,k1_funct_1(X1,X3))|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r2_hidden(X3,k10_relat_1(X1,k1_relat_1(X2)))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.41  cnf(c_0_63, negated_conjecture, (v1_funct_1(k4_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_27]), c_0_20]), c_0_21])])).
% 0.20/0.41  cnf(c_0_64, negated_conjecture, (k10_relat_1(k4_relat_1(esk5_0),k1_relat_1(esk5_0))=k1_relat_1(k4_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_56]), c_0_57]), c_0_58]), c_0_48])])).
% 0.20/0.41  cnf(c_0_65, negated_conjecture, (r2_hidden(esk4_0,k1_relat_1(k4_relat_1(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_32]), c_0_21])])).
% 0.20/0.41  cnf(c_0_66, negated_conjecture, (k1_funct_1(esk5_0,k1_funct_1(k4_relat_1(esk5_0),X1))=X1|~r2_hidden(X1,k2_relat_1(esk5_0))), inference(er,[status(thm)],[c_0_60])).
% 0.20/0.41  cnf(c_0_67, negated_conjecture, (k1_funct_1(esk5_0,k1_funct_1(k4_relat_1(esk5_0),esk4_0))!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_20]), c_0_48]), c_0_21]), c_0_64]), c_0_65])])).
% 0.20/0.41  cnf(c_0_68, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_59]), c_0_67]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 69
% 0.20/0.41  # Proof object clause steps            : 40
% 0.20/0.41  # Proof object formula steps           : 29
% 0.20/0.41  # Proof object conjectures             : 23
% 0.20/0.41  # Proof object clause conjectures      : 20
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 20
% 0.20/0.41  # Proof object initial formulas used   : 14
% 0.20/0.41  # Proof object generating inferences   : 19
% 0.20/0.41  # Proof object simplifying inferences  : 40
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 14
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 29
% 0.20/0.41  # Removed in clause preprocessing      : 0
% 0.20/0.41  # Initial clauses in saturation        : 29
% 0.20/0.41  # Processed clauses                    : 322
% 0.20/0.41  # ...of these trivial                  : 12
% 0.20/0.41  # ...subsumed                          : 62
% 0.20/0.41  # ...remaining for further processing  : 248
% 0.20/0.41  # Other redundant clauses eliminated   : 18
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 3
% 0.20/0.41  # Backward-rewritten                   : 6
% 0.20/0.41  # Generated clauses                    : 1124
% 0.20/0.41  # ...of the previous two non-trivial   : 1013
% 0.20/0.41  # Contextual simplify-reflections      : 6
% 0.20/0.41  # Paramodulations                      : 1067
% 0.20/0.41  # Factorizations                       : 6
% 0.20/0.41  # Equation resolutions                 : 51
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 211
% 0.20/0.41  #    Positive orientable unit clauses  : 40
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 1
% 0.20/0.41  #    Non-unit-clauses                  : 170
% 0.20/0.41  # Current number of unprocessed clauses: 745
% 0.20/0.41  # ...number of literals in the above   : 4493
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 37
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 2748
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 897
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 71
% 0.20/0.41  # Unit Clause-clause subsumption calls : 53
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 83
% 0.20/0.41  # BW rewrite match successes           : 5
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 32496
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.069 s
% 0.20/0.41  # System time              : 0.005 s
% 0.20/0.41  # Total time               : 0.074 s
% 0.20/0.41  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
