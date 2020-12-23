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
% DateTime   : Thu Dec  3 10:55:43 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 358 expanded)
%              Number of clauses        :   42 ( 148 expanded)
%              Number of leaves         :    9 (  83 expanded)
%              Depth                    :   14
%              Number of atoms          :  193 (1640 expanded)
%              Number of equality atoms :   23 ( 122 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t171_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ! [X3] :
              ( r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))
            <=> ( r1_tarski(X3,k1_relat_1(X1))
                & r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t156_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(t163_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(X1,k1_relat_1(X3))
          & r1_tarski(k9_relat_1(X3,X1),X2) )
       => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(d13_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( r2_hidden(X4,k1_relat_1(X1))
                & r2_hidden(k1_funct_1(X1,X4),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ! [X3] :
                ( r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))
              <=> ( r1_tarski(X3,k1_relat_1(X1))
                  & r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t171_funct_1])).

fof(c_0_10,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X19)
      | ~ v1_relat_1(X20)
      | k1_relat_1(k5_relat_1(X19,X20)) = k10_relat_1(X19,k1_relat_1(X20)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

fof(c_0_11,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & ( ~ r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))
      | ~ r1_tarski(esk5_0,k1_relat_1(esk3_0))
      | ~ r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)) )
    & ( r1_tarski(esk5_0,k1_relat_1(esk3_0))
      | r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0))) )
    & ( r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))
      | r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_13,plain,(
    ! [X14,X15] :
      ( ~ r1_tarski(X14,X15)
      | k2_xboole_0(X14,X15) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_14,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(k2_xboole_0(X11,X12),X13)
      | r1_tarski(X11,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(esk5_0,k1_relat_1(esk3_0))
    | r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk3_0,X1)) = k10_relat_1(esk3_0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_23,plain,(
    ! [X16,X17,X18] :
      ( ~ v1_relat_1(X18)
      | ~ r1_tarski(X16,X17)
      | r1_tarski(k9_relat_1(X18,X16),k9_relat_1(X18,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_26,plain,(
    ! [X31,X32,X33] :
      ( ~ v1_relat_1(X33)
      | ~ v1_funct_1(X33)
      | ~ r1_tarski(X31,k1_relat_1(X33))
      | ~ r1_tarski(k9_relat_1(X33,X31),X32)
      | r1_tarski(X31,k10_relat_1(X33,X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).

cnf(c_0_27,negated_conjecture,
    ( k2_xboole_0(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0))) = k1_relat_1(k5_relat_1(esk3_0,esk4_0))
    | r1_tarski(esk5_0,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk3_0,esk4_0)) = k10_relat_1(esk3_0,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))
    | r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( r1_tarski(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( k2_xboole_0(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0))) = k10_relat_1(esk3_0,k1_relat_1(esk4_0))
    | r1_tarski(esk5_0,k1_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,negated_conjecture,
    ( k2_xboole_0(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0))) = k1_relat_1(k5_relat_1(esk3_0,esk4_0))
    | r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_29])).

cnf(c_0_36,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,k2_xboole_0(X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( k2_xboole_0(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0))) = k10_relat_1(esk3_0,k1_relat_1(esk4_0))
    | r1_tarski(esk5_0,k10_relat_1(esk3_0,X1))
    | ~ r1_tarski(k9_relat_1(esk3_0,esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_15])])).

cnf(c_0_38,negated_conjecture,
    ( k2_xboole_0(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0))) = k10_relat_1(esk3_0,k1_relat_1(esk4_0))
    | r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_28]),c_0_28])).

fof(c_0_39,plain,(
    ! [X21,X22,X23,X24,X25,X26,X27] :
      ( ( r2_hidden(X24,k1_relat_1(X21))
        | ~ r2_hidden(X24,X23)
        | X23 != k10_relat_1(X21,X22)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( r2_hidden(k1_funct_1(X21,X24),X22)
        | ~ r2_hidden(X24,X23)
        | X23 != k10_relat_1(X21,X22)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( ~ r2_hidden(X25,k1_relat_1(X21))
        | ~ r2_hidden(k1_funct_1(X21,X25),X22)
        | r2_hidden(X25,X23)
        | X23 != k10_relat_1(X21,X22)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( ~ r2_hidden(esk2_3(X21,X26,X27),X27)
        | ~ r2_hidden(esk2_3(X21,X26,X27),k1_relat_1(X21))
        | ~ r2_hidden(k1_funct_1(X21,esk2_3(X21,X26,X27)),X26)
        | X27 = k10_relat_1(X21,X26)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( r2_hidden(esk2_3(X21,X26,X27),k1_relat_1(X21))
        | r2_hidden(esk2_3(X21,X26,X27),X27)
        | X27 = k10_relat_1(X21,X26)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( r2_hidden(k1_funct_1(X21,esk2_3(X21,X26,X27)),X26)
        | r2_hidden(esk2_3(X21,X26,X27),X27)
        | X27 = k10_relat_1(X21,X26)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,X1),k9_relat_1(esk3_0,k2_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_15])).

cnf(c_0_41,negated_conjecture,
    ( k2_xboole_0(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0))) = k10_relat_1(esk3_0,k1_relat_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_19])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,X3)
    | X3 != k10_relat_1(X2,X4)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,esk5_0),k9_relat_1(esk3_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_44,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X30)
      | ~ v1_funct_1(X30)
      | r1_tarski(k9_relat_1(X30,k10_relat_1(X30,X29)),X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k10_relat_1(X2,X3)) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))
    | ~ r1_tarski(esk5_0,k1_relat_1(esk3_0))
    | ~ r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_47,negated_conjecture,
    ( k2_xboole_0(k9_relat_1(esk3_0,esk5_0),k9_relat_1(esk3_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))) = k9_relat_1(esk3_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_43])).

cnf(c_0_48,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,plain,
    ( r2_hidden(esk1_2(k10_relat_1(X1,X2),X3),k1_relat_1(X1))
    | r1_tarski(k10_relat_1(X1,X2),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_18])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))
    | ~ r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))
    | ~ r1_tarski(esk5_0,k1_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_46,c_0_28])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,esk5_0),X1)
    | ~ r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0))),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_34]),c_0_15])])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk1_2(k10_relat_1(esk3_0,X1),X2),k1_relat_1(esk3_0))
    | r1_tarski(k10_relat_1(esk3_0,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_34]),c_0_15])])).

cnf(c_0_55,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))
    | ~ r1_tarski(esk5_0,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51])])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(esk5_0,X1)
    | ~ r1_tarski(k10_relat_1(esk3_0,k1_relat_1(esk4_0)),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_41])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,X1),k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( ~ r1_tarski(esk5_0,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56])])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:49:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.46  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.20/0.46  # and selection function SelectNewComplexAHP.
% 0.20/0.46  #
% 0.20/0.46  # Preprocessing time       : 0.028 s
% 0.20/0.46  # Presaturation interreduction done
% 0.20/0.46  
% 0.20/0.46  # Proof found!
% 0.20/0.46  # SZS status Theorem
% 0.20/0.46  # SZS output start CNFRefutation
% 0.20/0.46  fof(t171_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:(r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))<=>(r1_tarski(X3,k1_relat_1(X1))&r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_1)).
% 0.20/0.46  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 0.20/0.46  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.46  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.46  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.20/0.46  fof(t156_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 0.20/0.46  fof(t163_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(X1,k1_relat_1(X3))&r1_tarski(k9_relat_1(X3,X1),X2))=>r1_tarski(X1,k10_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 0.20/0.46  fof(d13_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,k1_relat_1(X1))&r2_hidden(k1_funct_1(X1,X4),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_funct_1)).
% 0.20/0.46  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 0.20/0.46  fof(c_0_9, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:(r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))<=>(r1_tarski(X3,k1_relat_1(X1))&r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2))))))), inference(assume_negation,[status(cth)],[t171_funct_1])).
% 0.20/0.46  fof(c_0_10, plain, ![X19, X20]:(~v1_relat_1(X19)|(~v1_relat_1(X20)|k1_relat_1(k5_relat_1(X19,X20))=k10_relat_1(X19,k1_relat_1(X20)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.20/0.46  fof(c_0_11, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&((~r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))|(~r1_tarski(esk5_0,k1_relat_1(esk3_0))|~r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))))&((r1_tarski(esk5_0,k1_relat_1(esk3_0))|r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0))))&(r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))|r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).
% 0.20/0.46  fof(c_0_12, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.46  fof(c_0_13, plain, ![X14, X15]:(~r1_tarski(X14,X15)|k2_xboole_0(X14,X15)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.46  cnf(c_0_14, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.46  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.46  fof(c_0_16, plain, ![X11, X12, X13]:(~r1_tarski(k2_xboole_0(X11,X12),X13)|r1_tarski(X11,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.20/0.46  cnf(c_0_17, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.46  cnf(c_0_18, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.46  cnf(c_0_19, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.46  cnf(c_0_20, negated_conjecture, (r1_tarski(esk5_0,k1_relat_1(esk3_0))|r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.46  cnf(c_0_21, negated_conjecture, (k1_relat_1(k5_relat_1(esk3_0,X1))=k10_relat_1(esk3_0,k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.46  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.46  fof(c_0_23, plain, ![X16, X17, X18]:(~v1_relat_1(X18)|(~r1_tarski(X16,X17)|r1_tarski(k9_relat_1(X18,X16),k9_relat_1(X18,X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).
% 0.20/0.46  cnf(c_0_24, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.46  cnf(c_0_25, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.46  fof(c_0_26, plain, ![X31, X32, X33]:(~v1_relat_1(X33)|~v1_funct_1(X33)|(~r1_tarski(X31,k1_relat_1(X33))|~r1_tarski(k9_relat_1(X33,X31),X32)|r1_tarski(X31,k10_relat_1(X33,X32)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).
% 0.20/0.46  cnf(c_0_27, negated_conjecture, (k2_xboole_0(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))=k1_relat_1(k5_relat_1(esk3_0,esk4_0))|r1_tarski(esk5_0,k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.46  cnf(c_0_28, negated_conjecture, (k1_relat_1(k5_relat_1(esk3_0,esk4_0))=k10_relat_1(esk3_0,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.46  cnf(c_0_29, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))|r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.46  cnf(c_0_30, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.46  cnf(c_0_31, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.46  cnf(c_0_32, plain, (r1_tarski(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~r1_tarski(k9_relat_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.46  cnf(c_0_33, negated_conjecture, (k2_xboole_0(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))=k10_relat_1(esk3_0,k1_relat_1(esk4_0))|r1_tarski(esk5_0,k1_relat_1(esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_28])).
% 0.20/0.46  cnf(c_0_34, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.46  cnf(c_0_35, negated_conjecture, (k2_xboole_0(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))=k1_relat_1(k5_relat_1(esk3_0,esk4_0))|r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_19, c_0_29])).
% 0.20/0.46  cnf(c_0_36, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,k2_xboole_0(X2,X3)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.46  cnf(c_0_37, negated_conjecture, (k2_xboole_0(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))=k10_relat_1(esk3_0,k1_relat_1(esk4_0))|r1_tarski(esk5_0,k10_relat_1(esk3_0,X1))|~r1_tarski(k9_relat_1(esk3_0,esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_15])])).
% 0.20/0.46  cnf(c_0_38, negated_conjecture, (k2_xboole_0(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))=k10_relat_1(esk3_0,k1_relat_1(esk4_0))|r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_28]), c_0_28])).
% 0.20/0.46  fof(c_0_39, plain, ![X21, X22, X23, X24, X25, X26, X27]:((((r2_hidden(X24,k1_relat_1(X21))|~r2_hidden(X24,X23)|X23!=k10_relat_1(X21,X22)|(~v1_relat_1(X21)|~v1_funct_1(X21)))&(r2_hidden(k1_funct_1(X21,X24),X22)|~r2_hidden(X24,X23)|X23!=k10_relat_1(X21,X22)|(~v1_relat_1(X21)|~v1_funct_1(X21))))&(~r2_hidden(X25,k1_relat_1(X21))|~r2_hidden(k1_funct_1(X21,X25),X22)|r2_hidden(X25,X23)|X23!=k10_relat_1(X21,X22)|(~v1_relat_1(X21)|~v1_funct_1(X21))))&((~r2_hidden(esk2_3(X21,X26,X27),X27)|(~r2_hidden(esk2_3(X21,X26,X27),k1_relat_1(X21))|~r2_hidden(k1_funct_1(X21,esk2_3(X21,X26,X27)),X26))|X27=k10_relat_1(X21,X26)|(~v1_relat_1(X21)|~v1_funct_1(X21)))&((r2_hidden(esk2_3(X21,X26,X27),k1_relat_1(X21))|r2_hidden(esk2_3(X21,X26,X27),X27)|X27=k10_relat_1(X21,X26)|(~v1_relat_1(X21)|~v1_funct_1(X21)))&(r2_hidden(k1_funct_1(X21,esk2_3(X21,X26,X27)),X26)|r2_hidden(esk2_3(X21,X26,X27),X27)|X27=k10_relat_1(X21,X26)|(~v1_relat_1(X21)|~v1_funct_1(X21)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).
% 0.20/0.46  cnf(c_0_40, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,X1),k9_relat_1(esk3_0,k2_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_36, c_0_15])).
% 0.20/0.46  cnf(c_0_41, negated_conjecture, (k2_xboole_0(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))=k10_relat_1(esk3_0,k1_relat_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_19])).
% 0.20/0.46  cnf(c_0_42, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,X3)|X3!=k10_relat_1(X2,X4)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.46  cnf(c_0_43, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,esk5_0),k9_relat_1(esk3_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0))))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.46  fof(c_0_44, plain, ![X29, X30]:(~v1_relat_1(X30)|~v1_funct_1(X30)|r1_tarski(k9_relat_1(X30,k10_relat_1(X30,X29)),X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.20/0.46  cnf(c_0_45, plain, (r2_hidden(X1,k1_relat_1(X2))|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k10_relat_1(X2,X3))), inference(er,[status(thm)],[c_0_42])).
% 0.20/0.46  cnf(c_0_46, negated_conjecture, (~r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))|~r1_tarski(esk5_0,k1_relat_1(esk3_0))|~r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.46  cnf(c_0_47, negated_conjecture, (k2_xboole_0(k9_relat_1(esk3_0,esk5_0),k9_relat_1(esk3_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0))))=k9_relat_1(esk3_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))), inference(spm,[status(thm)],[c_0_19, c_0_43])).
% 0.20/0.46  cnf(c_0_48, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.46  cnf(c_0_49, plain, (r2_hidden(esk1_2(k10_relat_1(X1,X2),X3),k1_relat_1(X1))|r1_tarski(k10_relat_1(X1,X2),X3)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_45, c_0_18])).
% 0.20/0.46  cnf(c_0_50, negated_conjecture, (~r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))|~r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))|~r1_tarski(esk5_0,k1_relat_1(esk3_0))), inference(rw,[status(thm)],[c_0_46, c_0_28])).
% 0.20/0.46  cnf(c_0_51, negated_conjecture, (r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))), inference(spm,[status(thm)],[c_0_31, c_0_41])).
% 0.20/0.46  cnf(c_0_52, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,esk5_0),X1)|~r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0))),X1)), inference(spm,[status(thm)],[c_0_24, c_0_47])).
% 0.20/0.46  cnf(c_0_53, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_34]), c_0_15])])).
% 0.20/0.46  cnf(c_0_54, negated_conjecture, (r2_hidden(esk1_2(k10_relat_1(esk3_0,X1),X2),k1_relat_1(esk3_0))|r1_tarski(k10_relat_1(esk3_0,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_34]), c_0_15])])).
% 0.20/0.46  cnf(c_0_55, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))|~r1_tarski(esk5_0,k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51])])).
% 0.20/0.46  cnf(c_0_56, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.46  cnf(c_0_57, negated_conjecture, (r1_tarski(esk5_0,X1)|~r1_tarski(k10_relat_1(esk3_0,k1_relat_1(esk4_0)),X1)), inference(spm,[status(thm)],[c_0_24, c_0_41])).
% 0.20/0.46  cnf(c_0_58, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,X1),k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_17, c_0_54])).
% 0.20/0.46  cnf(c_0_59, negated_conjecture, (~r1_tarski(esk5_0,k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56])])).
% 0.20/0.46  cnf(c_0_60, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), ['proof']).
% 0.20/0.46  # SZS output end CNFRefutation
% 0.20/0.46  # Proof object total steps             : 61
% 0.20/0.46  # Proof object clause steps            : 42
% 0.20/0.46  # Proof object formula steps           : 19
% 0.20/0.46  # Proof object conjectures             : 31
% 0.20/0.46  # Proof object clause conjectures      : 28
% 0.20/0.46  # Proof object formula conjectures     : 3
% 0.20/0.46  # Proof object initial clauses used    : 15
% 0.20/0.46  # Proof object initial formulas used   : 9
% 0.20/0.46  # Proof object generating inferences   : 21
% 0.20/0.46  # Proof object simplifying inferences  : 19
% 0.20/0.46  # Training examples: 0 positive, 0 negative
% 0.20/0.46  # Parsed axioms                        : 9
% 0.20/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.46  # Initial clauses                      : 22
% 0.20/0.46  # Removed in clause preprocessing      : 0
% 0.20/0.46  # Initial clauses in saturation        : 22
% 0.20/0.46  # Processed clauses                    : 656
% 0.20/0.46  # ...of these trivial                  : 37
% 0.20/0.46  # ...subsumed                          : 88
% 0.20/0.46  # ...remaining for further processing  : 531
% 0.20/0.46  # Other redundant clauses eliminated   : 3
% 0.20/0.46  # Clauses deleted for lack of memory   : 0
% 0.20/0.46  # Backward-subsumed                    : 99
% 0.20/0.46  # Backward-rewritten                   : 64
% 0.20/0.46  # Generated clauses                    : 2518
% 0.20/0.46  # ...of the previous two non-trivial   : 2325
% 0.20/0.46  # Contextual simplify-reflections      : 1
% 0.20/0.46  # Paramodulations                      : 2501
% 0.20/0.46  # Factorizations                       : 4
% 0.20/0.46  # Equation resolutions                 : 3
% 0.20/0.46  # Propositional unsat checks           : 0
% 0.20/0.46  #    Propositional check models        : 0
% 0.20/0.46  #    Propositional check unsatisfiable : 0
% 0.20/0.46  #    Propositional clauses             : 0
% 0.20/0.46  #    Propositional clauses after purity: 0
% 0.20/0.46  #    Propositional unsat core size     : 0
% 0.20/0.46  #    Propositional preprocessing time  : 0.000
% 0.20/0.46  #    Propositional encoding time       : 0.000
% 0.20/0.46  #    Propositional solver time         : 0.000
% 0.20/0.46  #    Success case prop preproc time    : 0.000
% 0.20/0.46  #    Success case prop encoding time   : 0.000
% 0.20/0.46  #    Success case prop solver time     : 0.000
% 0.20/0.46  # Current number of processed clauses  : 333
% 0.20/0.46  #    Positive orientable unit clauses  : 180
% 0.20/0.46  #    Positive unorientable unit clauses: 0
% 0.20/0.46  #    Negative unit clauses             : 1
% 0.20/0.46  #    Non-unit-clauses                  : 152
% 0.20/0.46  # Current number of unprocessed clauses: 1541
% 0.20/0.46  # ...number of literals in the above   : 3134
% 0.20/0.46  # Current number of archived formulas  : 0
% 0.20/0.46  # Current number of archived clauses   : 195
% 0.20/0.46  # Clause-clause subsumption calls (NU) : 6044
% 0.20/0.46  # Rec. Clause-clause subsumption calls : 4242
% 0.20/0.46  # Non-unit clause-clause subsumptions  : 158
% 0.20/0.46  # Unit Clause-clause subsumption calls : 1212
% 0.20/0.46  # Rewrite failures with RHS unbound    : 0
% 0.20/0.46  # BW rewrite match attempts            : 480
% 0.20/0.46  # BW rewrite match successes           : 19
% 0.20/0.46  # Condensation attempts                : 0
% 0.20/0.46  # Condensation successes               : 0
% 0.20/0.46  # Termbank termtop insertions          : 54642
% 0.20/0.46  
% 0.20/0.46  # -------------------------------------------------
% 0.20/0.46  # User time                : 0.105 s
% 0.20/0.46  # System time              : 0.006 s
% 0.20/0.46  # Total time               : 0.111 s
% 0.20/0.46  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
