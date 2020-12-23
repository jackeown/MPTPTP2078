%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:45 EST 2020

% Result     : Theorem 0.92s
% Output     : CNFRefutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 546 expanded)
%              Number of clauses        :   47 ( 210 expanded)
%              Number of leaves         :   12 ( 132 expanded)
%              Depth                    :   17
%              Number of atoms          :  197 (2539 expanded)
%              Number of equality atoms :   38 ( 164 expanded)
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

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t112_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k7_relat_1(k5_relat_1(X2,X3),X1) = k5_relat_1(k7_relat_1(X2,X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

fof(t44_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t89_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

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

fof(t46_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
           => k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(t27_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(X2)
           => r1_tarski(k2_relat_1(X2),k1_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(c_0_12,negated_conjecture,(
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

fof(c_0_13,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | ~ r1_tarski(X22,k1_relat_1(X23))
      | k1_relat_1(k7_relat_1(X23,X22)) = X22 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

fof(c_0_14,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).

cnf(c_0_15,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(esk3_0,k1_relat_1(esk1_0))
    | r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_17,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X7)
      | ~ v1_relat_1(X8)
      | v1_relat_1(k5_relat_1(X7,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_18,plain,(
    ! [X11,X12,X13] :
      ( ~ v1_relat_1(X12)
      | ~ v1_relat_1(X13)
      | k7_relat_1(k5_relat_1(X12,X13),X11) = k5_relat_1(k7_relat_1(X12,X11),X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).

cnf(c_0_19,negated_conjecture,
    ( k1_relat_1(k7_relat_1(k5_relat_1(esk1_0,esk2_0),esk3_0)) = esk3_0
    | r1_tarski(esk3_0,k1_relat_1(esk1_0))
    | ~ v1_relat_1(k5_relat_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k7_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( k1_relat_1(k7_relat_1(k5_relat_1(esk1_0,esk2_0),esk3_0)) = esk3_0
    | r1_tarski(esk3_0,k1_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])])).

cnf(c_0_25,negated_conjecture,
    ( k7_relat_1(k5_relat_1(esk1_0,X1),X2) = k5_relat_1(k7_relat_1(esk1_0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22])).

fof(c_0_26,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X16)
      | ~ v1_relat_1(X17)
      | r1_tarski(k1_relat_1(k5_relat_1(X16,X17)),k1_relat_1(X16)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_relat_1])])])).

cnf(c_0_27,negated_conjecture,
    ( k1_relat_1(k7_relat_1(k5_relat_1(esk1_0,esk2_0),esk3_0)) = esk3_0
    | k1_relat_1(k7_relat_1(esk1_0,esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_24]),c_0_22])])).

cnf(c_0_28,negated_conjecture,
    ( k7_relat_1(k5_relat_1(esk1_0,esk2_0),X1) = k5_relat_1(k7_relat_1(esk1_0,X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))
    | r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_30,plain,(
    ! [X4,X5,X6] :
      ( ~ r1_tarski(X4,X5)
      | ~ r1_tarski(X5,X6)
      | r1_tarski(X4,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_31,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X21)
      | r1_tarski(k1_relat_1(k7_relat_1(X21,X20)),k1_relat_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t89_relat_1])])).

cnf(c_0_32,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0)) = esk3_0
    | k1_relat_1(k7_relat_1(esk1_0,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_34,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X9)
      | v1_relat_1(k7_relat_1(X9,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_35,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X15)
      | k2_relat_1(k7_relat_1(X15,X14)) = k9_relat_1(X15,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_36,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,k9_relat_1(esk1_0,esk3_0))) = k9_relat_1(esk1_0,esk3_0)
    | r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_29]),c_0_21])])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk1_0,esk3_0)) = esk3_0
    | r1_tarski(esk3_0,k1_relat_1(k7_relat_1(esk1_0,esk3_0)))
    | ~ v1_relat_1(k7_relat_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_21])])).

cnf(c_0_40,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_41,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ v1_relat_1(X19)
      | ~ r1_tarski(k2_relat_1(X18),k1_relat_1(X19))
      | k1_relat_1(k5_relat_1(X18,X19)) = k1_relat_1(X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_relat_1])])])).

cnf(c_0_42,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,k9_relat_1(esk1_0,esk3_0))) = k9_relat_1(esk1_0,esk3_0)
    | k1_relat_1(k7_relat_1(k5_relat_1(esk1_0,esk2_0),esk3_0)) = esk3_0
    | ~ v1_relat_1(k5_relat_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_36])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k1_relat_1(k7_relat_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk1_0,esk3_0)) = esk3_0
    | r1_tarski(esk3_0,k1_relat_1(k7_relat_1(esk1_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_22])])).

cnf(c_0_46,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk1_0,X1)) = k9_relat_1(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_22])).

cnf(c_0_48,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,k9_relat_1(esk1_0,esk3_0))) = k9_relat_1(esk1_0,esk3_0)
    | k1_relat_1(k7_relat_1(k5_relat_1(esk1_0,esk2_0),esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_20]),c_0_21]),c_0_22])])).

cnf(c_0_49,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk1_0,esk3_0)) = esk3_0
    | r1_tarski(esk3_0,k1_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_22])])).

cnf(c_0_50,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,X1),X2)) = k1_relat_1(k7_relat_1(esk1_0,X1))
    | ~ v1_relat_1(k7_relat_1(esk1_0,X1))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k9_relat_1(esk1_0,X1),k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( k1_relat_1(k7_relat_1(k5_relat_1(esk1_0,esk2_0),esk3_0)) = esk3_0
    | r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_48]),c_0_21])])).

cnf(c_0_52,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk1_0,esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_49]),c_0_22])])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,X1),esk2_0)),k1_relat_1(k5_relat_1(esk1_0,esk2_0)))
    | ~ v1_relat_1(k5_relat_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_28])).

cnf(c_0_54,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,X1),X2)) = k1_relat_1(k7_relat_1(esk1_0,X1))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k9_relat_1(esk1_0,X1),k1_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_40]),c_0_22])])).

cnf(c_0_55,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0)) = esk3_0
    | r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_51,c_0_28])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))
    | ~ r1_tarski(esk3_0,k1_relat_1(esk1_0))
    | ~ r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(esk3_0,k1_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_52]),c_0_22])])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,X1),esk2_0)),k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_20]),c_0_21]),c_0_22])])).

cnf(c_0_59,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_52]),c_0_21])])).

fof(c_0_60,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X26)
      | ~ v1_funct_1(X26)
      | ~ v1_relat_1(X27)
      | ~ v1_funct_1(X27)
      | k1_relat_1(k5_relat_1(X27,X26)) != k1_relat_1(X27)
      | r1_tarski(k2_relat_1(X27),k1_relat_1(X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_funct_1])])])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))
    | ~ r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,plain,
    ( r1_tarski(k2_relat_1(X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_relat_1(k5_relat_1(X2,X1)) != k1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62])])).

fof(c_0_66,plain,(
    ! [X24,X25] :
      ( ( v1_relat_1(k7_relat_1(X24,X25))
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( v1_funct_1(k7_relat_1(X24,X25))
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

cnf(c_0_67,negated_conjecture,
    ( ~ v1_funct_1(k7_relat_1(esk1_0,esk3_0))
    | ~ v1_relat_1(k7_relat_1(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_59]),c_0_47]),c_0_52]),c_0_64]),c_0_21])]),c_0_65])).

cnf(c_0_68,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_70,negated_conjecture,
    ( ~ v1_relat_1(k7_relat_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69]),c_0_22])])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_40]),c_0_22])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:46:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.92/1.09  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S01BI
% 0.92/1.09  # and selection function PSelectMinOptimalNoXTypePred.
% 0.92/1.09  #
% 0.92/1.09  # Preprocessing time       : 0.027 s
% 0.92/1.09  # Presaturation interreduction done
% 0.92/1.09  
% 0.92/1.09  # Proof found!
% 0.92/1.09  # SZS status Theorem
% 0.92/1.09  # SZS output start CNFRefutation
% 0.92/1.09  fof(t171_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:(r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))<=>(r1_tarski(X3,k1_relat_1(X1))&r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_1)).
% 0.92/1.09  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 0.92/1.09  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.92/1.09  fof(t112_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k7_relat_1(k5_relat_1(X2,X3),X1)=k5_relat_1(k7_relat_1(X2,X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 0.92/1.09  fof(t44_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 0.92/1.09  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.92/1.09  fof(t89_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),k1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 0.92/1.09  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.92/1.09  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.92/1.09  fof(t46_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X1),k1_relat_1(X2))=>k1_relat_1(k5_relat_1(X1,X2))=k1_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 0.92/1.09  fof(t27_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(k5_relat_1(X2,X1))=k1_relat_1(X2)=>r1_tarski(k2_relat_1(X2),k1_relat_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_funct_1)).
% 0.92/1.09  fof(fc8_funct_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k7_relat_1(X1,X2))&v1_funct_1(k7_relat_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 0.92/1.09  fof(c_0_12, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:(r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))<=>(r1_tarski(X3,k1_relat_1(X1))&r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2))))))), inference(assume_negation,[status(cth)],[t171_funct_1])).
% 0.92/1.09  fof(c_0_13, plain, ![X22, X23]:(~v1_relat_1(X23)|(~r1_tarski(X22,k1_relat_1(X23))|k1_relat_1(k7_relat_1(X23,X22))=X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 0.92/1.09  fof(c_0_14, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&((~r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))|(~r1_tarski(esk3_0,k1_relat_1(esk1_0))|~r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))))&((r1_tarski(esk3_0,k1_relat_1(esk1_0))|r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))))&(r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))|r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).
% 0.92/1.09  cnf(c_0_15, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.92/1.09  cnf(c_0_16, negated_conjecture, (r1_tarski(esk3_0,k1_relat_1(esk1_0))|r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.92/1.09  fof(c_0_17, plain, ![X7, X8]:(~v1_relat_1(X7)|~v1_relat_1(X8)|v1_relat_1(k5_relat_1(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.92/1.09  fof(c_0_18, plain, ![X11, X12, X13]:(~v1_relat_1(X12)|(~v1_relat_1(X13)|k7_relat_1(k5_relat_1(X12,X13),X11)=k5_relat_1(k7_relat_1(X12,X11),X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).
% 0.92/1.09  cnf(c_0_19, negated_conjecture, (k1_relat_1(k7_relat_1(k5_relat_1(esk1_0,esk2_0),esk3_0))=esk3_0|r1_tarski(esk3_0,k1_relat_1(esk1_0))|~v1_relat_1(k5_relat_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.92/1.09  cnf(c_0_20, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.92/1.09  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.92/1.09  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.92/1.09  cnf(c_0_23, plain, (k7_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.92/1.09  cnf(c_0_24, negated_conjecture, (k1_relat_1(k7_relat_1(k5_relat_1(esk1_0,esk2_0),esk3_0))=esk3_0|r1_tarski(esk3_0,k1_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])])).
% 0.92/1.09  cnf(c_0_25, negated_conjecture, (k7_relat_1(k5_relat_1(esk1_0,X1),X2)=k5_relat_1(k7_relat_1(esk1_0,X2),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_23, c_0_22])).
% 0.92/1.09  fof(c_0_26, plain, ![X16, X17]:(~v1_relat_1(X16)|(~v1_relat_1(X17)|r1_tarski(k1_relat_1(k5_relat_1(X16,X17)),k1_relat_1(X16)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_relat_1])])])).
% 0.92/1.09  cnf(c_0_27, negated_conjecture, (k1_relat_1(k7_relat_1(k5_relat_1(esk1_0,esk2_0),esk3_0))=esk3_0|k1_relat_1(k7_relat_1(esk1_0,esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_24]), c_0_22])])).
% 0.92/1.09  cnf(c_0_28, negated_conjecture, (k7_relat_1(k5_relat_1(esk1_0,esk2_0),X1)=k5_relat_1(k7_relat_1(esk1_0,X1),esk2_0)), inference(spm,[status(thm)],[c_0_25, c_0_21])).
% 0.92/1.09  cnf(c_0_29, negated_conjecture, (r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))|r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.92/1.09  fof(c_0_30, plain, ![X4, X5, X6]:(~r1_tarski(X4,X5)|~r1_tarski(X5,X6)|r1_tarski(X4,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.92/1.09  fof(c_0_31, plain, ![X20, X21]:(~v1_relat_1(X21)|r1_tarski(k1_relat_1(k7_relat_1(X21,X20)),k1_relat_1(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t89_relat_1])])).
% 0.92/1.09  cnf(c_0_32, plain, (r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.92/1.09  cnf(c_0_33, negated_conjecture, (k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0))=esk3_0|k1_relat_1(k7_relat_1(esk1_0,esk3_0))=esk3_0), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.92/1.09  fof(c_0_34, plain, ![X9, X10]:(~v1_relat_1(X9)|v1_relat_1(k7_relat_1(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.92/1.09  fof(c_0_35, plain, ![X14, X15]:(~v1_relat_1(X15)|k2_relat_1(k7_relat_1(X15,X14))=k9_relat_1(X15,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.92/1.09  cnf(c_0_36, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,k9_relat_1(esk1_0,esk3_0)))=k9_relat_1(esk1_0,esk3_0)|r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_29]), c_0_21])])).
% 0.92/1.09  cnf(c_0_37, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.92/1.09  cnf(c_0_38, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.92/1.09  cnf(c_0_39, negated_conjecture, (k1_relat_1(k7_relat_1(esk1_0,esk3_0))=esk3_0|r1_tarski(esk3_0,k1_relat_1(k7_relat_1(esk1_0,esk3_0)))|~v1_relat_1(k7_relat_1(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_21])])).
% 0.92/1.09  cnf(c_0_40, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.92/1.09  fof(c_0_41, plain, ![X18, X19]:(~v1_relat_1(X18)|(~v1_relat_1(X19)|(~r1_tarski(k2_relat_1(X18),k1_relat_1(X19))|k1_relat_1(k5_relat_1(X18,X19))=k1_relat_1(X18)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_relat_1])])])).
% 0.92/1.09  cnf(c_0_42, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.92/1.09  cnf(c_0_43, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,k9_relat_1(esk1_0,esk3_0)))=k9_relat_1(esk1_0,esk3_0)|k1_relat_1(k7_relat_1(k5_relat_1(esk1_0,esk2_0),esk3_0))=esk3_0|~v1_relat_1(k5_relat_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_15, c_0_36])).
% 0.92/1.09  cnf(c_0_44, plain, (r1_tarski(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,k1_relat_1(k7_relat_1(X2,X3)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.92/1.09  cnf(c_0_45, negated_conjecture, (k1_relat_1(k7_relat_1(esk1_0,esk3_0))=esk3_0|r1_tarski(esk3_0,k1_relat_1(k7_relat_1(esk1_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_22])])).
% 0.92/1.09  cnf(c_0_46, plain, (k1_relat_1(k5_relat_1(X1,X2))=k1_relat_1(X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(k2_relat_1(X1),k1_relat_1(X2))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.92/1.09  cnf(c_0_47, negated_conjecture, (k2_relat_1(k7_relat_1(esk1_0,X1))=k9_relat_1(esk1_0,X1)), inference(spm,[status(thm)],[c_0_42, c_0_22])).
% 0.92/1.09  cnf(c_0_48, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,k9_relat_1(esk1_0,esk3_0)))=k9_relat_1(esk1_0,esk3_0)|k1_relat_1(k7_relat_1(k5_relat_1(esk1_0,esk2_0),esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_20]), c_0_21]), c_0_22])])).
% 0.92/1.09  cnf(c_0_49, negated_conjecture, (k1_relat_1(k7_relat_1(esk1_0,esk3_0))=esk3_0|r1_tarski(esk3_0,k1_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_22])])).
% 0.92/1.09  cnf(c_0_50, negated_conjecture, (k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,X1),X2))=k1_relat_1(k7_relat_1(esk1_0,X1))|~v1_relat_1(k7_relat_1(esk1_0,X1))|~v1_relat_1(X2)|~r1_tarski(k9_relat_1(esk1_0,X1),k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.92/1.09  cnf(c_0_51, negated_conjecture, (k1_relat_1(k7_relat_1(k5_relat_1(esk1_0,esk2_0),esk3_0))=esk3_0|r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_48]), c_0_21])])).
% 0.92/1.09  cnf(c_0_52, negated_conjecture, (k1_relat_1(k7_relat_1(esk1_0,esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_49]), c_0_22])])).
% 0.92/1.09  cnf(c_0_53, negated_conjecture, (r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,X1),esk2_0)),k1_relat_1(k5_relat_1(esk1_0,esk2_0)))|~v1_relat_1(k5_relat_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_38, c_0_28])).
% 0.92/1.09  cnf(c_0_54, negated_conjecture, (k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,X1),X2))=k1_relat_1(k7_relat_1(esk1_0,X1))|~v1_relat_1(X2)|~r1_tarski(k9_relat_1(esk1_0,X1),k1_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_40]), c_0_22])])).
% 0.92/1.09  cnf(c_0_55, negated_conjecture, (k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0))=esk3_0|r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))), inference(rw,[status(thm)],[c_0_51, c_0_28])).
% 0.92/1.09  cnf(c_0_56, negated_conjecture, (~r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))|~r1_tarski(esk3_0,k1_relat_1(esk1_0))|~r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.92/1.09  cnf(c_0_57, negated_conjecture, (r1_tarski(esk3_0,k1_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_52]), c_0_22])])).
% 0.92/1.09  cnf(c_0_58, negated_conjecture, (r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,X1),esk2_0)),k1_relat_1(k5_relat_1(esk1_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_20]), c_0_21]), c_0_22])])).
% 0.92/1.09  cnf(c_0_59, negated_conjecture, (k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_52]), c_0_21])])).
% 0.92/1.09  fof(c_0_60, plain, ![X26, X27]:(~v1_relat_1(X26)|~v1_funct_1(X26)|(~v1_relat_1(X27)|~v1_funct_1(X27)|(k1_relat_1(k5_relat_1(X27,X26))!=k1_relat_1(X27)|r1_tarski(k2_relat_1(X27),k1_relat_1(X26))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_funct_1])])])).
% 0.92/1.09  cnf(c_0_61, negated_conjecture, (~r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))|~r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57])])).
% 0.92/1.09  cnf(c_0_62, negated_conjecture, (r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.92/1.09  cnf(c_0_63, plain, (r1_tarski(k2_relat_1(X2),k1_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k1_relat_1(k5_relat_1(X2,X1))!=k1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.92/1.09  cnf(c_0_64, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.92/1.09  cnf(c_0_65, negated_conjecture, (~r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62])])).
% 0.92/1.09  fof(c_0_66, plain, ![X24, X25]:((v1_relat_1(k7_relat_1(X24,X25))|(~v1_relat_1(X24)|~v1_funct_1(X24)))&(v1_funct_1(k7_relat_1(X24,X25))|(~v1_relat_1(X24)|~v1_funct_1(X24)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).
% 0.92/1.09  cnf(c_0_67, negated_conjecture, (~v1_funct_1(k7_relat_1(esk1_0,esk3_0))|~v1_relat_1(k7_relat_1(esk1_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_59]), c_0_47]), c_0_52]), c_0_64]), c_0_21])]), c_0_65])).
% 0.92/1.09  cnf(c_0_68, plain, (v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.92/1.09  cnf(c_0_69, negated_conjecture, (v1_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.92/1.09  cnf(c_0_70, negated_conjecture, (~v1_relat_1(k7_relat_1(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69]), c_0_22])])).
% 0.92/1.09  cnf(c_0_71, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_40]), c_0_22])]), ['proof']).
% 0.92/1.09  # SZS output end CNFRefutation
% 0.92/1.09  # Proof object total steps             : 72
% 0.92/1.09  # Proof object clause steps            : 47
% 0.92/1.09  # Proof object formula steps           : 25
% 0.92/1.09  # Proof object conjectures             : 38
% 0.92/1.09  # Proof object clause conjectures      : 35
% 0.92/1.09  # Proof object formula conjectures     : 3
% 0.92/1.09  # Proof object initial clauses used    : 18
% 0.92/1.09  # Proof object initial formulas used   : 12
% 0.92/1.09  # Proof object generating inferences   : 25
% 0.92/1.09  # Proof object simplifying inferences  : 47
% 0.92/1.09  # Training examples: 0 positive, 0 negative
% 0.92/1.09  # Parsed axioms                        : 12
% 0.92/1.09  # Removed by relevancy pruning/SinE    : 0
% 0.92/1.09  # Initial clauses                      : 19
% 0.92/1.09  # Removed in clause preprocessing      : 0
% 0.92/1.09  # Initial clauses in saturation        : 19
% 0.92/1.09  # Processed clauses                    : 5145
% 0.92/1.09  # ...of these trivial                  : 142
% 0.92/1.09  # ...subsumed                          : 2145
% 0.92/1.09  # ...remaining for further processing  : 2858
% 0.92/1.09  # Other redundant clauses eliminated   : 0
% 0.92/1.09  # Clauses deleted for lack of memory   : 0
% 0.92/1.09  # Backward-subsumed                    : 824
% 0.92/1.09  # Backward-rewritten                   : 79
% 0.92/1.09  # Generated clauses                    : 36941
% 0.92/1.09  # ...of the previous two non-trivial   : 36562
% 0.92/1.09  # Contextual simplify-reflections      : 5
% 0.92/1.09  # Paramodulations                      : 36938
% 0.92/1.09  # Factorizations                       : 3
% 0.92/1.09  # Equation resolutions                 : 0
% 0.92/1.09  # Propositional unsat checks           : 0
% 0.92/1.09  #    Propositional check models        : 0
% 0.92/1.09  #    Propositional check unsatisfiable : 0
% 0.92/1.09  #    Propositional clauses             : 0
% 0.92/1.09  #    Propositional clauses after purity: 0
% 0.92/1.09  #    Propositional unsat core size     : 0
% 0.92/1.09  #    Propositional preprocessing time  : 0.000
% 0.92/1.09  #    Propositional encoding time       : 0.000
% 0.92/1.09  #    Propositional solver time         : 0.000
% 0.92/1.09  #    Success case prop preproc time    : 0.000
% 0.92/1.09  #    Success case prop encoding time   : 0.000
% 0.92/1.09  #    Success case prop solver time     : 0.000
% 0.92/1.09  # Current number of processed clauses  : 1937
% 0.92/1.09  #    Positive orientable unit clauses  : 370
% 0.92/1.09  #    Positive unorientable unit clauses: 0
% 0.92/1.09  #    Negative unit clauses             : 59
% 0.92/1.09  #    Non-unit-clauses                  : 1508
% 0.92/1.09  # Current number of unprocessed clauses: 31126
% 0.92/1.09  # ...number of literals in the above   : 119564
% 0.92/1.09  # Current number of archived formulas  : 0
% 0.92/1.09  # Current number of archived clauses   : 921
% 0.92/1.09  # Clause-clause subsumption calls (NU) : 555202
% 0.92/1.09  # Rec. Clause-clause subsumption calls : 100529
% 0.92/1.09  # Non-unit clause-clause subsumptions  : 2808
% 0.92/1.09  # Unit Clause-clause subsumption calls : 39066
% 0.92/1.09  # Rewrite failures with RHS unbound    : 0
% 0.92/1.09  # BW rewrite match attempts            : 10167
% 0.92/1.09  # BW rewrite match successes           : 68
% 0.92/1.09  # Condensation attempts                : 0
% 0.92/1.09  # Condensation successes               : 0
% 0.92/1.09  # Termbank termtop insertions          : 1095124
% 0.92/1.10  
% 0.92/1.10  # -------------------------------------------------
% 0.92/1.10  # User time                : 0.732 s
% 0.92/1.10  # System time              : 0.034 s
% 0.92/1.10  # Total time               : 0.766 s
% 0.92/1.10  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
