%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:44 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 270 expanded)
%              Number of clauses        :   44 ( 101 expanded)
%              Number of leaves         :   16 (  67 expanded)
%              Depth                    :   15
%              Number of atoms          :  204 (1237 expanded)
%              Number of equality atoms :   31 (  55 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   11 (   2 average)
%              Maximal term depth       :    4 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t44_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(t163_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(X1,k1_relat_1(X3))
          & r1_tarski(k9_relat_1(X3,X1),X2) )
       => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(t112_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k7_relat_1(k5_relat_1(X2,X3),X1) = k5_relat_1(k7_relat_1(X2,X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

fof(fc2_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k5_relat_1(X1,X2))
        & v1_funct_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(c_0_16,negated_conjecture,(
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

fof(c_0_17,plain,(
    ! [X7,X8] :
      ( ~ r1_tarski(X7,X8)
      | k2_xboole_0(X7,X8) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_18,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & ( ~ r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))
      | ~ r1_tarski(esk3_0,k1_relat_1(esk1_0))
      | ~ r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0)) )
    & ( r1_tarski(esk3_0,k1_relat_1(esk1_0))
      | r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) )
    & ( r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))
      | r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])])).

fof(c_0_19,plain,(
    ! [X4,X5,X6] :
      ( ~ r1_tarski(k2_xboole_0(X4,X5),X6)
      | r1_tarski(X4,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk3_0,k1_relat_1(esk1_0))
    | r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( k2_xboole_0(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) = k1_relat_1(k5_relat_1(esk1_0,esk2_0))
    | r1_tarski(esk3_0,k1_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_24,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | ~ v1_relat_1(X21)
      | r1_tarski(k1_relat_1(k5_relat_1(X20,X21)),k1_relat_1(X20)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_relat_1])])])).

fof(c_0_25,plain,(
    ! [X32,X33,X34] :
      ( ~ v1_relat_1(X34)
      | ~ v1_funct_1(X34)
      | ~ r1_tarski(X32,k1_relat_1(X34))
      | ~ r1_tarski(k9_relat_1(X34,X32),X33)
      | r1_tarski(X32,k10_relat_1(X34,X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(esk3_0,k1_relat_1(esk1_0))
    | r1_tarski(esk3_0,X1)
    | ~ r1_tarski(k1_relat_1(k5_relat_1(esk1_0,esk2_0)),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_30,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | ~ r1_tarski(X22,k1_relat_1(X23))
      | k1_relat_1(k7_relat_1(X23,X22)) = X22 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

cnf(c_0_31,plain,
    ( r1_tarski(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk3_0,k1_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_34,plain,(
    ! [X26] :
      ( ~ v1_relat_1(X26)
      | k7_relat_1(X26,k1_relat_1(X26)) = X26 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

cnf(c_0_35,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk3_0,k10_relat_1(esk1_0,X1))
    | ~ r1_tarski(k9_relat_1(esk1_0,esk3_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_29])])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))
    | r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_38,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ v1_relat_1(X19)
      | k1_relat_1(k5_relat_1(X18,X19)) = k10_relat_1(X18,k1_relat_1(X19)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

cnf(c_0_39,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk1_0,esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_32]),c_0_29])])).

fof(c_0_41,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | v1_relat_1(k7_relat_1(X11,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))
    | r1_tarski(esk3_0,k10_relat_1(esk1_0,k1_relat_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_44,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X17)
      | k2_relat_1(k7_relat_1(X17,X16)) = k9_relat_1(X17,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_45,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk1_0,esk3_0),esk3_0) = k7_relat_1(esk1_0,esk3_0)
    | ~ v1_relat_1(k7_relat_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_28]),c_0_29])])).

fof(c_0_48,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X9)
      | ~ v1_relat_1(X10)
      | v1_relat_1(k5_relat_1(X9,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_49,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk1_0,esk3_0),esk3_0) = k7_relat_1(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_29])])).

fof(c_0_51,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X31)
      | ~ v1_funct_1(X31)
      | r1_tarski(k9_relat_1(X31,k10_relat_1(X31,X30)),X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

cnf(c_0_52,negated_conjecture,
    ( k1_relat_1(k7_relat_1(k5_relat_1(esk1_0,esk2_0),esk3_0)) = esk3_0
    | ~ v1_relat_1(k5_relat_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_47])).

cnf(c_0_53,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_54,plain,(
    ! [X13,X14,X15] :
      ( ~ v1_relat_1(X14)
      | ~ v1_relat_1(X15)
      | k7_relat_1(k5_relat_1(X14,X15),X13) = k5_relat_1(k7_relat_1(X14,X13),X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).

cnf(c_0_55,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk1_0,esk3_0)) = k9_relat_1(k7_relat_1(esk1_0,esk3_0),esk3_0)
    | ~ v1_relat_1(k7_relat_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))
    | ~ r1_tarski(esk3_0,k1_relat_1(esk1_0))
    | ~ r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_57,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( k1_relat_1(k7_relat_1(k5_relat_1(esk1_0,esk2_0),esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_28]),c_0_29])])).

cnf(c_0_59,plain,
    ( k7_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk1_0,esk3_0)) = k9_relat_1(k7_relat_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_46]),c_0_29])])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))
    | ~ r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_32])])).

fof(c_0_62,plain,(
    ! [X27,X28] :
      ( ( v1_relat_1(k5_relat_1(X27,X28))
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( v1_funct_1(k5_relat_1(X27,X28))
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).

fof(c_0_63,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | k7_relat_1(X25,X24) = k5_relat_1(k6_relat_1(X24),X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_64,plain,(
    ! [X29] :
      ( v1_relat_1(k6_relat_1(X29))
      & v1_funct_1(k6_relat_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_65,plain,
    ( r1_tarski(k9_relat_1(X1,k1_relat_1(k5_relat_1(X1,X2))),k1_relat_1(X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_43])).

cnf(c_0_66,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_28]),c_0_29])])).

cnf(c_0_67,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk1_0,esk3_0),esk3_0) = k9_relat_1(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_60]),c_0_29])])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_47])])).

cnf(c_0_69,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_70,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_71,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_72,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_73,negated_conjecture,
    ( ~ v1_funct_1(k7_relat_1(esk1_0,esk3_0))
    | ~ v1_relat_1(k7_relat_1(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_28])]),c_0_68])).

cnf(c_0_74,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_72])])).

cnf(c_0_75,negated_conjecture,
    ( ~ v1_relat_1(k7_relat_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_33]),c_0_29])])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_46]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S2q
% 0.19/0.40  # and selection function SelectCQArNTNp.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.042 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t171_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:(r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))<=>(r1_tarski(X3,k1_relat_1(X1))&r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_1)).
% 0.19/0.40  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.40  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.19/0.40  fof(t44_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 0.19/0.40  fof(t163_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(X1,k1_relat_1(X3))&r1_tarski(k9_relat_1(X3,X1),X2))=>r1_tarski(X1,k10_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 0.19/0.40  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 0.19/0.40  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 0.19/0.40  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 0.19/0.40  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.19/0.40  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.19/0.40  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.19/0.40  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 0.19/0.40  fof(t112_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k7_relat_1(k5_relat_1(X2,X3),X1)=k5_relat_1(k7_relat_1(X2,X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 0.19/0.40  fof(fc2_funct_1, axiom, ![X1, X2]:((((v1_relat_1(X1)&v1_funct_1(X1))&v1_relat_1(X2))&v1_funct_1(X2))=>(v1_relat_1(k5_relat_1(X1,X2))&v1_funct_1(k5_relat_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funct_1)).
% 0.19/0.40  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.19/0.40  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.19/0.40  fof(c_0_16, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:(r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))<=>(r1_tarski(X3,k1_relat_1(X1))&r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2))))))), inference(assume_negation,[status(cth)],[t171_funct_1])).
% 0.19/0.40  fof(c_0_17, plain, ![X7, X8]:(~r1_tarski(X7,X8)|k2_xboole_0(X7,X8)=X8), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.40  fof(c_0_18, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&((~r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))|(~r1_tarski(esk3_0,k1_relat_1(esk1_0))|~r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))))&((r1_tarski(esk3_0,k1_relat_1(esk1_0))|r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))))&(r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))|r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])])).
% 0.19/0.40  fof(c_0_19, plain, ![X4, X5, X6]:(~r1_tarski(k2_xboole_0(X4,X5),X6)|r1_tarski(X4,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.19/0.40  cnf(c_0_20, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_21, negated_conjecture, (r1_tarski(esk3_0,k1_relat_1(esk1_0))|r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.40  cnf(c_0_22, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_23, negated_conjecture, (k2_xboole_0(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))=k1_relat_1(k5_relat_1(esk1_0,esk2_0))|r1_tarski(esk3_0,k1_relat_1(esk1_0))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.40  fof(c_0_24, plain, ![X20, X21]:(~v1_relat_1(X20)|(~v1_relat_1(X21)|r1_tarski(k1_relat_1(k5_relat_1(X20,X21)),k1_relat_1(X20)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_relat_1])])])).
% 0.19/0.40  fof(c_0_25, plain, ![X32, X33, X34]:(~v1_relat_1(X34)|~v1_funct_1(X34)|(~r1_tarski(X32,k1_relat_1(X34))|~r1_tarski(k9_relat_1(X34,X32),X33)|r1_tarski(X32,k10_relat_1(X34,X33)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).
% 0.19/0.40  cnf(c_0_26, negated_conjecture, (r1_tarski(esk3_0,k1_relat_1(esk1_0))|r1_tarski(esk3_0,X1)|~r1_tarski(k1_relat_1(k5_relat_1(esk1_0,esk2_0)),X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.40  cnf(c_0_27, plain, (r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.40  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.40  cnf(c_0_29, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.40  fof(c_0_30, plain, ![X22, X23]:(~v1_relat_1(X23)|(~r1_tarski(X22,k1_relat_1(X23))|k1_relat_1(k7_relat_1(X23,X22))=X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 0.19/0.40  cnf(c_0_31, plain, (r1_tarski(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~r1_tarski(k9_relat_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.40  cnf(c_0_32, negated_conjecture, (r1_tarski(esk3_0,k1_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])])).
% 0.19/0.40  cnf(c_0_33, negated_conjecture, (v1_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.40  fof(c_0_34, plain, ![X26]:(~v1_relat_1(X26)|k7_relat_1(X26,k1_relat_1(X26))=X26), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.19/0.40  cnf(c_0_35, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.40  cnf(c_0_36, negated_conjecture, (r1_tarski(esk3_0,k10_relat_1(esk1_0,X1))|~r1_tarski(k9_relat_1(esk1_0,esk3_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_29])])).
% 0.19/0.40  cnf(c_0_37, negated_conjecture, (r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))|r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.40  fof(c_0_38, plain, ![X18, X19]:(~v1_relat_1(X18)|(~v1_relat_1(X19)|k1_relat_1(k5_relat_1(X18,X19))=k10_relat_1(X18,k1_relat_1(X19)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.19/0.40  cnf(c_0_39, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.40  cnf(c_0_40, negated_conjecture, (k1_relat_1(k7_relat_1(esk1_0,esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_32]), c_0_29])])).
% 0.19/0.40  fof(c_0_41, plain, ![X11, X12]:(~v1_relat_1(X11)|v1_relat_1(k7_relat_1(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.19/0.40  cnf(c_0_42, negated_conjecture, (r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))|r1_tarski(esk3_0,k10_relat_1(esk1_0,k1_relat_1(esk2_0)))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.40  cnf(c_0_43, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.40  fof(c_0_44, plain, ![X16, X17]:(~v1_relat_1(X17)|k2_relat_1(k7_relat_1(X17,X16))=k9_relat_1(X17,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.19/0.40  cnf(c_0_45, negated_conjecture, (k7_relat_1(k7_relat_1(esk1_0,esk3_0),esk3_0)=k7_relat_1(esk1_0,esk3_0)|~v1_relat_1(k7_relat_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.40  cnf(c_0_46, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.40  cnf(c_0_47, negated_conjecture, (r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_28]), c_0_29])])).
% 0.19/0.40  fof(c_0_48, plain, ![X9, X10]:(~v1_relat_1(X9)|~v1_relat_1(X10)|v1_relat_1(k5_relat_1(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.19/0.40  cnf(c_0_49, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.40  cnf(c_0_50, negated_conjecture, (k7_relat_1(k7_relat_1(esk1_0,esk3_0),esk3_0)=k7_relat_1(esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_29])])).
% 0.19/0.40  fof(c_0_51, plain, ![X30, X31]:(~v1_relat_1(X31)|~v1_funct_1(X31)|r1_tarski(k9_relat_1(X31,k10_relat_1(X31,X30)),X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.19/0.40  cnf(c_0_52, negated_conjecture, (k1_relat_1(k7_relat_1(k5_relat_1(esk1_0,esk2_0),esk3_0))=esk3_0|~v1_relat_1(k5_relat_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_35, c_0_47])).
% 0.19/0.40  cnf(c_0_53, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.40  fof(c_0_54, plain, ![X13, X14, X15]:(~v1_relat_1(X14)|(~v1_relat_1(X15)|k7_relat_1(k5_relat_1(X14,X15),X13)=k5_relat_1(k7_relat_1(X14,X13),X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).
% 0.19/0.40  cnf(c_0_55, negated_conjecture, (k2_relat_1(k7_relat_1(esk1_0,esk3_0))=k9_relat_1(k7_relat_1(esk1_0,esk3_0),esk3_0)|~v1_relat_1(k7_relat_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.40  cnf(c_0_56, negated_conjecture, (~r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))|~r1_tarski(esk3_0,k1_relat_1(esk1_0))|~r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.40  cnf(c_0_57, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.40  cnf(c_0_58, negated_conjecture, (k1_relat_1(k7_relat_1(k5_relat_1(esk1_0,esk2_0),esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_28]), c_0_29])])).
% 0.19/0.40  cnf(c_0_59, plain, (k7_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.40  cnf(c_0_60, negated_conjecture, (k2_relat_1(k7_relat_1(esk1_0,esk3_0))=k9_relat_1(k7_relat_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_46]), c_0_29])])).
% 0.19/0.40  cnf(c_0_61, negated_conjecture, (~r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))|~r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_32])])).
% 0.19/0.40  fof(c_0_62, plain, ![X27, X28]:((v1_relat_1(k5_relat_1(X27,X28))|(~v1_relat_1(X27)|~v1_funct_1(X27)|~v1_relat_1(X28)|~v1_funct_1(X28)))&(v1_funct_1(k5_relat_1(X27,X28))|(~v1_relat_1(X27)|~v1_funct_1(X27)|~v1_relat_1(X28)|~v1_funct_1(X28)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).
% 0.19/0.40  fof(c_0_63, plain, ![X24, X25]:(~v1_relat_1(X25)|k7_relat_1(X25,X24)=k5_relat_1(k6_relat_1(X24),X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.19/0.40  fof(c_0_64, plain, ![X29]:(v1_relat_1(k6_relat_1(X29))&v1_funct_1(k6_relat_1(X29))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.19/0.40  cnf(c_0_65, plain, (r1_tarski(k9_relat_1(X1,k1_relat_1(k5_relat_1(X1,X2))),k1_relat_1(X2))|~v1_funct_1(X1)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_57, c_0_43])).
% 0.19/0.40  cnf(c_0_66, negated_conjecture, (k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_28]), c_0_29])])).
% 0.19/0.40  cnf(c_0_67, negated_conjecture, (k9_relat_1(k7_relat_1(esk1_0,esk3_0),esk3_0)=k9_relat_1(esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_60]), c_0_29])])).
% 0.19/0.40  cnf(c_0_68, negated_conjecture, (~r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_47])])).
% 0.19/0.40  cnf(c_0_69, plain, (v1_funct_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.40  cnf(c_0_70, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.40  cnf(c_0_71, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.40  cnf(c_0_72, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.40  cnf(c_0_73, negated_conjecture, (~v1_funct_1(k7_relat_1(esk1_0,esk3_0))|~v1_relat_1(k7_relat_1(esk1_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_28])]), c_0_68])).
% 0.19/0.40  cnf(c_0_74, plain, (v1_funct_1(k7_relat_1(X1,X2))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71]), c_0_72])])).
% 0.19/0.40  cnf(c_0_75, negated_conjecture, (~v1_relat_1(k7_relat_1(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_33]), c_0_29])])).
% 0.19/0.40  cnf(c_0_76, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_46]), c_0_29])]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 77
% 0.19/0.40  # Proof object clause steps            : 44
% 0.19/0.40  # Proof object formula steps           : 33
% 0.19/0.40  # Proof object conjectures             : 29
% 0.19/0.40  # Proof object clause conjectures      : 26
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 22
% 0.19/0.40  # Proof object initial formulas used   : 16
% 0.19/0.40  # Proof object generating inferences   : 20
% 0.19/0.40  # Proof object simplifying inferences  : 39
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 16
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 24
% 0.19/0.40  # Removed in clause preprocessing      : 0
% 0.19/0.40  # Initial clauses in saturation        : 24
% 0.19/0.40  # Processed clauses                    : 141
% 0.19/0.40  # ...of these trivial                  : 3
% 0.19/0.40  # ...subsumed                          : 12
% 0.19/0.40  # ...remaining for further processing  : 126
% 0.19/0.40  # Other redundant clauses eliminated   : 0
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 3
% 0.19/0.40  # Backward-rewritten                   : 19
% 0.19/0.40  # Generated clauses                    : 305
% 0.19/0.40  # ...of the previous two non-trivial   : 273
% 0.19/0.40  # Contextual simplify-reflections      : 2
% 0.19/0.40  # Paramodulations                      : 305
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 0
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 81
% 0.19/0.40  #    Positive orientable unit clauses  : 32
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 2
% 0.19/0.40  #    Non-unit-clauses                  : 47
% 0.19/0.40  # Current number of unprocessed clauses: 169
% 0.19/0.40  # ...number of literals in the above   : 609
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 45
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 614
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 466
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 17
% 0.19/0.40  # Unit Clause-clause subsumption calls : 16
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 26
% 0.19/0.40  # BW rewrite match successes           : 9
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 7603
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.058 s
% 0.19/0.40  # System time              : 0.006 s
% 0.19/0.40  # Total time               : 0.064 s
% 0.19/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
