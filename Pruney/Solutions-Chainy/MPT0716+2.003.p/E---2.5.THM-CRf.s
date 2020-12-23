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
% DateTime   : Thu Dec  3 10:55:43 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 221 expanded)
%              Number of clauses        :   34 (  84 expanded)
%              Number of leaves         :   10 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :  196 (1151 expanded)
%              Number of equality atoms :   13 (  30 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   19 (   2 average)
%              Maximal term depth       :    5 (   1 average)

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

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t163_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(X1,k1_relat_1(X3))
          & r1_tarski(k9_relat_1(X3,X1),X2) )
       => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(t158_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ! [X4] :
          ( v1_relat_1(X4)
         => ( ( r1_tarski(X3,X4)
              & r1_tarski(X1,X2) )
           => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(c_0_10,negated_conjecture,(
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

fof(c_0_11,plain,(
    ! [X16,X17] :
      ( ~ r1_tarski(X16,X17)
      | k2_xboole_0(X16,X17) = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & ( ~ r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))
      | ~ r1_tarski(esk4_0,k1_relat_1(esk2_0))
      | ~ r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0)) )
    & ( r1_tarski(esk4_0,k1_relat_1(esk2_0))
      | r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0))) )
    & ( r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))
      | r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X29,X30,X31] :
      ( ( r2_hidden(X29,k1_relat_1(X31))
        | ~ r2_hidden(X29,k1_relat_1(k5_relat_1(X31,X30)))
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) )
      & ( r2_hidden(k1_funct_1(X31,X29),k1_relat_1(X30))
        | ~ r2_hidden(X29,k1_relat_1(k5_relat_1(X31,X30)))
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) )
      & ( ~ r2_hidden(X29,k1_relat_1(X31))
        | ~ r2_hidden(k1_funct_1(X31,X29),k1_relat_1(X30))
        | r2_hidden(X29,k1_relat_1(k5_relat_1(X31,X30)))
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_funct_1])])])])).

fof(c_0_14,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_15,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(k2_xboole_0(X13,X14),X15)
      | r1_tarski(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk4_0,k1_relat_1(esk2_0))
    | r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( k2_xboole_0(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0))) = k1_relat_1(k5_relat_1(esk2_0,esk3_0))
    | r1_tarski(esk4_0,k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_2(k1_relat_1(k5_relat_1(X1,X2)),X3),k1_relat_1(X1))
    | r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_24,plain,(
    ! [X26,X27,X28] :
      ( ~ v1_relat_1(X28)
      | ~ v1_funct_1(X28)
      | ~ r1_tarski(X26,k1_relat_1(X28))
      | ~ r1_tarski(k9_relat_1(X28,X26),X27)
      | r1_tarski(X26,k10_relat_1(X28,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk4_0,k1_relat_1(esk2_0))
    | r1_tarski(esk4_0,X1)
    | ~ r1_tarski(k1_relat_1(k5_relat_1(esk2_0,esk3_0)),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_31,plain,
    ( r1_tarski(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk4_0,k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30])])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk4_0,k10_relat_1(esk2_0,X1))
    | ~ r1_tarski(k9_relat_1(esk2_0,esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_28]),c_0_30])])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))
    | r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_35,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X22)
      | ~ v1_relat_1(X23)
      | k1_relat_1(k5_relat_1(X22,X23)) = k10_relat_1(X22,k1_relat_1(X23)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

fof(c_0_36,plain,(
    ! [X18,X19,X20,X21] :
      ( ~ v1_relat_1(X20)
      | ~ v1_relat_1(X21)
      | ~ r1_tarski(X20,X21)
      | ~ r1_tarski(X18,X19)
      | r1_tarski(k9_relat_1(X20,X18),k9_relat_1(X21,X19)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_relat_1])])])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))
    | r1_tarski(esk4_0,k10_relat_1(esk2_0,k1_relat_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_39,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_40,plain,
    ( r1_tarski(k9_relat_1(X1,X3),k9_relat_1(X2,X4))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_29]),c_0_30])])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k9_relat_1(X1,esk4_0),k9_relat_1(X2,k1_relat_1(k5_relat_1(esk2_0,esk3_0))))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k9_relat_1(X1,esk4_0),k9_relat_1(X1,k1_relat_1(k5_relat_1(esk2_0,esk3_0))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_46,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | ~ v1_funct_1(X25)
      | r1_tarski(k9_relat_1(X25,k10_relat_1(X25,X24)),X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))
    | ~ r1_tarski(esk4_0,k1_relat_1(esk2_0))
    | ~ r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_48,negated_conjecture,
    ( k2_xboole_0(k9_relat_1(X1,esk4_0),k9_relat_1(X1,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))) = k9_relat_1(X1,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_45])).

cnf(c_0_49,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))
    | ~ r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_32])])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k9_relat_1(X1,esk4_0),X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k9_relat_1(X1,k1_relat_1(k5_relat_1(esk2_0,esk3_0))),X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_48])).

cnf(c_0_52,plain,
    ( r1_tarski(k9_relat_1(X1,k1_relat_1(k5_relat_1(X1,X2))),k1_relat_1(X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_38])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_41])])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_30]),c_0_28]),c_0_29])]),c_0_53]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:11:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.40  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2S
% 0.18/0.40  # and selection function SelectNewComplexAHP.
% 0.18/0.40  #
% 0.18/0.40  # Preprocessing time       : 0.016 s
% 0.18/0.40  # Presaturation interreduction done
% 0.18/0.40  
% 0.18/0.40  # Proof found!
% 0.18/0.40  # SZS status Theorem
% 0.18/0.40  # SZS output start CNFRefutation
% 0.18/0.40  fof(t171_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:(r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))<=>(r1_tarski(X3,k1_relat_1(X1))&r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_1)).
% 0.18/0.40  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.18/0.40  fof(t21_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_1)).
% 0.18/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.18/0.40  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.18/0.40  fof(t163_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(X1,k1_relat_1(X3))&r1_tarski(k9_relat_1(X3,X1),X2))=>r1_tarski(X1,k10_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 0.18/0.40  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 0.18/0.40  fof(t158_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_relat_1)).
% 0.18/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.18/0.40  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 0.18/0.40  fof(c_0_10, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:(r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))<=>(r1_tarski(X3,k1_relat_1(X1))&r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2))))))), inference(assume_negation,[status(cth)],[t171_funct_1])).
% 0.18/0.40  fof(c_0_11, plain, ![X16, X17]:(~r1_tarski(X16,X17)|k2_xboole_0(X16,X17)=X17), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.18/0.40  fof(c_0_12, negated_conjecture, ((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((~r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))|(~r1_tarski(esk4_0,k1_relat_1(esk2_0))|~r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))))&((r1_tarski(esk4_0,k1_relat_1(esk2_0))|r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0))))&(r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))|r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).
% 0.18/0.40  fof(c_0_13, plain, ![X29, X30, X31]:(((r2_hidden(X29,k1_relat_1(X31))|~r2_hidden(X29,k1_relat_1(k5_relat_1(X31,X30)))|(~v1_relat_1(X31)|~v1_funct_1(X31))|(~v1_relat_1(X30)|~v1_funct_1(X30)))&(r2_hidden(k1_funct_1(X31,X29),k1_relat_1(X30))|~r2_hidden(X29,k1_relat_1(k5_relat_1(X31,X30)))|(~v1_relat_1(X31)|~v1_funct_1(X31))|(~v1_relat_1(X30)|~v1_funct_1(X30))))&(~r2_hidden(X29,k1_relat_1(X31))|~r2_hidden(k1_funct_1(X31,X29),k1_relat_1(X30))|r2_hidden(X29,k1_relat_1(k5_relat_1(X31,X30)))|(~v1_relat_1(X31)|~v1_funct_1(X31))|(~v1_relat_1(X30)|~v1_funct_1(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_funct_1])])])])).
% 0.18/0.40  fof(c_0_14, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.18/0.40  fof(c_0_15, plain, ![X13, X14, X15]:(~r1_tarski(k2_xboole_0(X13,X14),X15)|r1_tarski(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.18/0.40  cnf(c_0_16, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.40  cnf(c_0_17, negated_conjecture, (r1_tarski(esk4_0,k1_relat_1(esk2_0))|r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.40  cnf(c_0_18, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X3)|~v1_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.40  cnf(c_0_19, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.40  cnf(c_0_20, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.40  cnf(c_0_21, negated_conjecture, (k2_xboole_0(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))=k1_relat_1(k5_relat_1(esk2_0,esk3_0))|r1_tarski(esk4_0,k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.18/0.40  cnf(c_0_22, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.40  cnf(c_0_23, plain, (r2_hidden(esk1_2(k1_relat_1(k5_relat_1(X1,X2)),X3),k1_relat_1(X1))|r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),X3)|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.18/0.40  fof(c_0_24, plain, ![X26, X27, X28]:(~v1_relat_1(X28)|~v1_funct_1(X28)|(~r1_tarski(X26,k1_relat_1(X28))|~r1_tarski(k9_relat_1(X28,X26),X27)|r1_tarski(X26,k10_relat_1(X28,X27)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).
% 0.18/0.40  cnf(c_0_25, negated_conjecture, (r1_tarski(esk4_0,k1_relat_1(esk2_0))|r1_tarski(esk4_0,X1)|~r1_tarski(k1_relat_1(k5_relat_1(esk2_0,esk3_0)),X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.18/0.40  cnf(c_0_26, plain, (r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1))|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.18/0.40  cnf(c_0_27, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.40  cnf(c_0_28, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.40  cnf(c_0_29, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.40  cnf(c_0_30, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.40  cnf(c_0_31, plain, (r1_tarski(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~r1_tarski(k9_relat_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.40  cnf(c_0_32, negated_conjecture, (r1_tarski(esk4_0,k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30])])).
% 0.18/0.40  cnf(c_0_33, negated_conjecture, (r1_tarski(esk4_0,k10_relat_1(esk2_0,X1))|~r1_tarski(k9_relat_1(esk2_0,esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_28]), c_0_30])])).
% 0.18/0.40  cnf(c_0_34, negated_conjecture, (r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))|r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.40  fof(c_0_35, plain, ![X22, X23]:(~v1_relat_1(X22)|(~v1_relat_1(X23)|k1_relat_1(k5_relat_1(X22,X23))=k10_relat_1(X22,k1_relat_1(X23)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.18/0.40  fof(c_0_36, plain, ![X18, X19, X20, X21]:(~v1_relat_1(X20)|(~v1_relat_1(X21)|(~r1_tarski(X20,X21)|~r1_tarski(X18,X19)|r1_tarski(k9_relat_1(X20,X18),k9_relat_1(X21,X19))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_relat_1])])])).
% 0.18/0.40  cnf(c_0_37, negated_conjecture, (r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))|r1_tarski(esk4_0,k10_relat_1(esk2_0,k1_relat_1(esk3_0)))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.18/0.40  cnf(c_0_38, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.40  fof(c_0_39, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.18/0.40  cnf(c_0_40, plain, (r1_tarski(k9_relat_1(X1,X3),k9_relat_1(X2,X4))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.18/0.40  cnf(c_0_41, negated_conjecture, (r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_29]), c_0_30])])).
% 0.18/0.40  cnf(c_0_42, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.18/0.40  cnf(c_0_43, negated_conjecture, (r1_tarski(k9_relat_1(X1,esk4_0),k9_relat_1(X2,k1_relat_1(k5_relat_1(esk2_0,esk3_0))))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.18/0.40  cnf(c_0_44, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_42])).
% 0.18/0.40  cnf(c_0_45, negated_conjecture, (r1_tarski(k9_relat_1(X1,esk4_0),k9_relat_1(X1,k1_relat_1(k5_relat_1(esk2_0,esk3_0))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.18/0.40  fof(c_0_46, plain, ![X24, X25]:(~v1_relat_1(X25)|~v1_funct_1(X25)|r1_tarski(k9_relat_1(X25,k10_relat_1(X25,X24)),X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.18/0.40  cnf(c_0_47, negated_conjecture, (~r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))|~r1_tarski(esk4_0,k1_relat_1(esk2_0))|~r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.40  cnf(c_0_48, negated_conjecture, (k2_xboole_0(k9_relat_1(X1,esk4_0),k9_relat_1(X1,k1_relat_1(k5_relat_1(esk2_0,esk3_0))))=k9_relat_1(X1,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_16, c_0_45])).
% 0.18/0.40  cnf(c_0_49, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.18/0.40  cnf(c_0_50, negated_conjecture, (~r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))|~r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_32])])).
% 0.18/0.40  cnf(c_0_51, negated_conjecture, (r1_tarski(k9_relat_1(X1,esk4_0),X2)|~v1_relat_1(X1)|~r1_tarski(k9_relat_1(X1,k1_relat_1(k5_relat_1(esk2_0,esk3_0))),X2)), inference(spm,[status(thm)],[c_0_20, c_0_48])).
% 0.18/0.40  cnf(c_0_52, plain, (r1_tarski(k9_relat_1(X1,k1_relat_1(k5_relat_1(X1,X2))),k1_relat_1(X2))|~v1_funct_1(X1)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_49, c_0_38])).
% 0.18/0.40  cnf(c_0_53, negated_conjecture, (~r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_41])])).
% 0.18/0.40  cnf(c_0_54, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_30]), c_0_28]), c_0_29])]), c_0_53]), ['proof']).
% 0.18/0.40  # SZS output end CNFRefutation
% 0.18/0.40  # Proof object total steps             : 55
% 0.18/0.40  # Proof object clause steps            : 34
% 0.18/0.40  # Proof object formula steps           : 21
% 0.18/0.40  # Proof object conjectures             : 23
% 0.18/0.40  # Proof object clause conjectures      : 20
% 0.18/0.40  # Proof object formula conjectures     : 3
% 0.18/0.40  # Proof object initial clauses used    : 17
% 0.18/0.40  # Proof object initial formulas used   : 10
% 0.18/0.40  # Proof object generating inferences   : 14
% 0.18/0.40  # Proof object simplifying inferences  : 21
% 0.18/0.40  # Training examples: 0 positive, 0 negative
% 0.18/0.40  # Parsed axioms                        : 10
% 0.18/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.40  # Initial clauses                      : 22
% 0.18/0.40  # Removed in clause preprocessing      : 0
% 0.18/0.40  # Initial clauses in saturation        : 22
% 0.18/0.40  # Processed clauses                    : 679
% 0.18/0.40  # ...of these trivial                  : 26
% 0.18/0.40  # ...subsumed                          : 288
% 0.18/0.40  # ...remaining for further processing  : 365
% 0.18/0.40  # Other redundant clauses eliminated   : 2
% 0.18/0.40  # Clauses deleted for lack of memory   : 0
% 0.18/0.40  # Backward-subsumed                    : 0
% 0.18/0.40  # Backward-rewritten                   : 29
% 0.18/0.40  # Generated clauses                    : 2487
% 0.18/0.40  # ...of the previous two non-trivial   : 2297
% 0.18/0.40  # Contextual simplify-reflections      : 0
% 0.18/0.40  # Paramodulations                      : 2485
% 0.18/0.40  # Factorizations                       : 0
% 0.18/0.40  # Equation resolutions                 : 2
% 0.18/0.40  # Propositional unsat checks           : 0
% 0.18/0.40  #    Propositional check models        : 0
% 0.18/0.40  #    Propositional check unsatisfiable : 0
% 0.18/0.40  #    Propositional clauses             : 0
% 0.18/0.40  #    Propositional clauses after purity: 0
% 0.18/0.40  #    Propositional unsat core size     : 0
% 0.18/0.40  #    Propositional preprocessing time  : 0.000
% 0.18/0.40  #    Propositional encoding time       : 0.000
% 0.18/0.40  #    Propositional solver time         : 0.000
% 0.18/0.40  #    Success case prop preproc time    : 0.000
% 0.18/0.40  #    Success case prop encoding time   : 0.000
% 0.18/0.40  #    Success case prop solver time     : 0.000
% 0.18/0.40  # Current number of processed clauses  : 313
% 0.18/0.40  #    Positive orientable unit clauses  : 51
% 0.18/0.40  #    Positive unorientable unit clauses: 0
% 0.18/0.40  #    Negative unit clauses             : 1
% 0.18/0.40  #    Non-unit-clauses                  : 261
% 0.18/0.40  # Current number of unprocessed clauses: 1598
% 0.18/0.40  # ...number of literals in the above   : 5760
% 0.18/0.40  # Current number of archived formulas  : 0
% 0.18/0.40  # Current number of archived clauses   : 50
% 0.18/0.40  # Clause-clause subsumption calls (NU) : 10135
% 0.18/0.40  # Rec. Clause-clause subsumption calls : 6251
% 0.18/0.40  # Non-unit clause-clause subsumptions  : 288
% 0.18/0.40  # Unit Clause-clause subsumption calls : 1037
% 0.18/0.40  # Rewrite failures with RHS unbound    : 0
% 0.18/0.40  # BW rewrite match attempts            : 124
% 0.18/0.40  # BW rewrite match successes           : 2
% 0.18/0.40  # Condensation attempts                : 0
% 0.18/0.40  # Condensation successes               : 0
% 0.18/0.40  # Termbank termtop insertions          : 51224
% 0.18/0.40  
% 0.18/0.40  # -------------------------------------------------
% 0.18/0.40  # User time                : 0.057 s
% 0.18/0.40  # System time              : 0.006 s
% 0.18/0.40  # Total time               : 0.064 s
% 0.18/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
