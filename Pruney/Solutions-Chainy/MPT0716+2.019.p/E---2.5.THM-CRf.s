%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:45 EST 2020

% Result     : Theorem 0.84s
% Output     : CNFRefutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 448 expanded)
%              Number of clauses        :   47 ( 176 expanded)
%              Number of leaves         :   13 ( 108 expanded)
%              Depth                    :   14
%              Number of atoms          :  195 (2011 expanded)
%              Number of equality atoms :   39 ( 150 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   11 (   2 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_1)).

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(t44_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t112_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k7_relat_1(k5_relat_1(X2,X3),X1) = k5_relat_1(k7_relat_1(X2,X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t89_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

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

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

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

fof(c_0_13,negated_conjecture,(
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

fof(c_0_14,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | ~ r1_tarski(X24,k1_relat_1(X25))
      | k1_relat_1(k7_relat_1(X25,X24)) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

fof(c_0_15,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ v1_relat_1(X19)
      | r1_tarski(k1_relat_1(k5_relat_1(X18,X19)),k1_relat_1(X18)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_relat_1])])])).

fof(c_0_16,plain,(
    ! [X7,X8] :
      ( ~ r1_tarski(X7,X8)
      | k2_xboole_0(X7,X8) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_17,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).

cnf(c_0_18,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X13,X14,X15] :
      ( ~ v1_relat_1(X14)
      | ~ v1_relat_1(X15)
      | k7_relat_1(k5_relat_1(X14,X15),X13) = k5_relat_1(k7_relat_1(X14,X13),X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk3_0,k1_relat_1(esk1_0))
    | r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k1_relat_1(k7_relat_1(X1,k1_relat_1(k5_relat_1(X1,X2)))) = k1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k7_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_27,plain,(
    ! [X4,X5,X6] :
      ( ~ r1_tarski(k2_xboole_0(X4,X5),X6)
      | r1_tarski(X4,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_28,negated_conjecture,
    ( k2_xboole_0(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) = k1_relat_1(k5_relat_1(esk1_0,esk2_0))
    | r1_tarski(esk3_0,k1_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_29,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | r1_tarski(k1_relat_1(k7_relat_1(X23,X22)),k1_relat_1(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t89_relat_1])])).

cnf(c_0_30,negated_conjecture,
    ( k1_relat_1(k7_relat_1(X1,k1_relat_1(k5_relat_1(X1,esk2_0)))) = k1_relat_1(k5_relat_1(X1,esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_31,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X17)
      | k2_relat_1(k7_relat_1(X17,X16)) = k9_relat_1(X17,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))
    | r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( k7_relat_1(k5_relat_1(esk1_0,X1),X2) = k5_relat_1(k7_relat_1(esk1_0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( k2_xboole_0(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) = k1_relat_1(k5_relat_1(esk1_0,esk2_0))
    | k1_relat_1(k7_relat_1(esk1_0,esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_28]),c_0_26])])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk1_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))) = k1_relat_1(k5_relat_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_26])).

fof(c_0_38,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | ~ v1_relat_1(X21)
      | ~ r1_tarski(k2_relat_1(X20),k1_relat_1(X21))
      | k1_relat_1(k5_relat_1(X20,X21)) = k1_relat_1(X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_relat_1])])])).

cnf(c_0_39,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,k9_relat_1(esk1_0,esk3_0))) = k9_relat_1(esk1_0,esk3_0)
    | r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_32]),c_0_24])])).

cnf(c_0_41,negated_conjecture,
    ( k7_relat_1(k5_relat_1(esk1_0,esk2_0),X1) = k5_relat_1(k7_relat_1(esk1_0,X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_24])).

fof(c_0_42,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X9)
      | ~ v1_relat_1(X10)
      | v1_relat_1(k5_relat_1(X9,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_43,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk1_0,esk3_0)) = esk3_0
    | r1_tarski(esk3_0,X1)
    | ~ r1_tarski(k1_relat_1(k5_relat_1(esk1_0,esk2_0)),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k1_relat_1(k5_relat_1(esk1_0,esk2_0)),k1_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_26])])).

cnf(c_0_45,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk1_0,X1)) = k9_relat_1(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_26])).

fof(c_0_47,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | v1_relat_1(k7_relat_1(X11,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_48,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,k9_relat_1(esk1_0,esk3_0))) = k9_relat_1(esk1_0,esk3_0)
    | k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0)) = esk3_0
    | ~ v1_relat_1(k5_relat_1(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_40]),c_0_41])).

cnf(c_0_49,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk1_0,esk3_0)) = esk3_0
    | r1_tarski(esk3_0,k1_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,X1),X2)) = k1_relat_1(k7_relat_1(esk1_0,X1))
    | ~ v1_relat_1(k7_relat_1(esk1_0,X1))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k9_relat_1(esk1_0,X1),k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,k9_relat_1(esk1_0,esk3_0))) = k9_relat_1(esk1_0,esk3_0)
    | k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_24]),c_0_26])])).

cnf(c_0_54,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk1_0,esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_50]),c_0_26])])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,X1),esk2_0)),k1_relat_1(k5_relat_1(esk1_0,esk2_0)))
    | ~ v1_relat_1(k5_relat_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_41])).

cnf(c_0_56,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,X1),X2)) = k1_relat_1(k7_relat_1(esk1_0,X1))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k9_relat_1(esk1_0,X1),k1_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_26])])).

cnf(c_0_57,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0)) = esk3_0
    | r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_53]),c_0_24])])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))
    | ~ r1_tarski(esk3_0,k1_relat_1(esk1_0))
    | ~ r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(esk3_0,k1_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_54]),c_0_26])])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,X1),esk2_0)),k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_49]),c_0_24]),c_0_26])])).

cnf(c_0_61,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_54]),c_0_24])])).

fof(c_0_62,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X28)
      | ~ v1_funct_1(X28)
      | ~ v1_relat_1(X29)
      | ~ v1_funct_1(X29)
      | k1_relat_1(k5_relat_1(X29,X28)) != k1_relat_1(X29)
      | r1_tarski(k2_relat_1(X29),k1_relat_1(X28)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_funct_1])])])).

cnf(c_0_63,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))
    | ~ r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59])])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_65,plain,
    ( r1_tarski(k2_relat_1(X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_relat_1(k5_relat_1(X2,X1)) != k1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_67,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64])])).

fof(c_0_68,plain,(
    ! [X26,X27] :
      ( ( v1_relat_1(k7_relat_1(X26,X27))
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( v1_funct_1(k7_relat_1(X26,X27))
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_funct_1(k7_relat_1(esk1_0,esk3_0))
    | ~ v1_relat_1(k7_relat_1(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_61]),c_0_46]),c_0_54]),c_0_66]),c_0_24])]),c_0_67])).

cnf(c_0_70,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_72,negated_conjecture,
    ( ~ v1_relat_1(k7_relat_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_26])])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_52]),c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:53:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.84/1.06  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S01BI
% 0.84/1.06  # and selection function PSelectMinOptimalNoXTypePred.
% 0.84/1.06  #
% 0.84/1.06  # Preprocessing time       : 0.041 s
% 0.84/1.06  # Presaturation interreduction done
% 0.84/1.06  
% 0.84/1.06  # Proof found!
% 0.84/1.06  # SZS status Theorem
% 0.84/1.06  # SZS output start CNFRefutation
% 0.84/1.06  fof(t171_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:(r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))<=>(r1_tarski(X3,k1_relat_1(X1))&r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_1)).
% 0.84/1.06  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 0.84/1.06  fof(t44_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 0.84/1.06  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.84/1.06  fof(t112_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k7_relat_1(k5_relat_1(X2,X3),X1)=k5_relat_1(k7_relat_1(X2,X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 0.84/1.06  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.84/1.06  fof(t89_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),k1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 0.84/1.06  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.84/1.06  fof(t46_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X1),k1_relat_1(X2))=>k1_relat_1(k5_relat_1(X1,X2))=k1_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 0.84/1.06  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.84/1.06  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.84/1.06  fof(t27_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(k5_relat_1(X2,X1))=k1_relat_1(X2)=>r1_tarski(k2_relat_1(X2),k1_relat_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_funct_1)).
% 0.84/1.06  fof(fc8_funct_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k7_relat_1(X1,X2))&v1_funct_1(k7_relat_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 0.84/1.06  fof(c_0_13, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:(r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))<=>(r1_tarski(X3,k1_relat_1(X1))&r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2))))))), inference(assume_negation,[status(cth)],[t171_funct_1])).
% 0.84/1.06  fof(c_0_14, plain, ![X24, X25]:(~v1_relat_1(X25)|(~r1_tarski(X24,k1_relat_1(X25))|k1_relat_1(k7_relat_1(X25,X24))=X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 0.84/1.06  fof(c_0_15, plain, ![X18, X19]:(~v1_relat_1(X18)|(~v1_relat_1(X19)|r1_tarski(k1_relat_1(k5_relat_1(X18,X19)),k1_relat_1(X18)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_relat_1])])])).
% 0.84/1.06  fof(c_0_16, plain, ![X7, X8]:(~r1_tarski(X7,X8)|k2_xboole_0(X7,X8)=X8), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.84/1.06  fof(c_0_17, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&((~r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))|(~r1_tarski(esk3_0,k1_relat_1(esk1_0))|~r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))))&((r1_tarski(esk3_0,k1_relat_1(esk1_0))|r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))))&(r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))|r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).
% 0.84/1.06  cnf(c_0_18, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.84/1.06  cnf(c_0_19, plain, (r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.84/1.06  fof(c_0_20, plain, ![X13, X14, X15]:(~v1_relat_1(X14)|(~v1_relat_1(X15)|k7_relat_1(k5_relat_1(X14,X15),X13)=k5_relat_1(k7_relat_1(X14,X13),X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).
% 0.84/1.06  cnf(c_0_21, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.84/1.06  cnf(c_0_22, negated_conjecture, (r1_tarski(esk3_0,k1_relat_1(esk1_0))|r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.84/1.06  cnf(c_0_23, plain, (k1_relat_1(k7_relat_1(X1,k1_relat_1(k5_relat_1(X1,X2))))=k1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.84/1.06  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.84/1.06  cnf(c_0_25, plain, (k7_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.84/1.06  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.84/1.06  fof(c_0_27, plain, ![X4, X5, X6]:(~r1_tarski(k2_xboole_0(X4,X5),X6)|r1_tarski(X4,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.84/1.06  cnf(c_0_28, negated_conjecture, (k2_xboole_0(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))=k1_relat_1(k5_relat_1(esk1_0,esk2_0))|r1_tarski(esk3_0,k1_relat_1(esk1_0))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.84/1.06  fof(c_0_29, plain, ![X22, X23]:(~v1_relat_1(X23)|r1_tarski(k1_relat_1(k7_relat_1(X23,X22)),k1_relat_1(X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t89_relat_1])])).
% 0.84/1.06  cnf(c_0_30, negated_conjecture, (k1_relat_1(k7_relat_1(X1,k1_relat_1(k5_relat_1(X1,esk2_0))))=k1_relat_1(k5_relat_1(X1,esk2_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.84/1.06  fof(c_0_31, plain, ![X16, X17]:(~v1_relat_1(X17)|k2_relat_1(k7_relat_1(X17,X16))=k9_relat_1(X17,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.84/1.06  cnf(c_0_32, negated_conjecture, (r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))|r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.84/1.06  cnf(c_0_33, negated_conjecture, (k7_relat_1(k5_relat_1(esk1_0,X1),X2)=k5_relat_1(k7_relat_1(esk1_0,X2),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.84/1.06  cnf(c_0_34, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.84/1.06  cnf(c_0_35, negated_conjecture, (k2_xboole_0(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))=k1_relat_1(k5_relat_1(esk1_0,esk2_0))|k1_relat_1(k7_relat_1(esk1_0,esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_28]), c_0_26])])).
% 0.84/1.06  cnf(c_0_36, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.84/1.06  cnf(c_0_37, negated_conjecture, (k1_relat_1(k7_relat_1(esk1_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))))=k1_relat_1(k5_relat_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_30, c_0_26])).
% 0.84/1.06  fof(c_0_38, plain, ![X20, X21]:(~v1_relat_1(X20)|(~v1_relat_1(X21)|(~r1_tarski(k2_relat_1(X20),k1_relat_1(X21))|k1_relat_1(k5_relat_1(X20,X21))=k1_relat_1(X20)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_relat_1])])])).
% 0.84/1.06  cnf(c_0_39, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.84/1.06  cnf(c_0_40, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,k9_relat_1(esk1_0,esk3_0)))=k9_relat_1(esk1_0,esk3_0)|r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_32]), c_0_24])])).
% 0.84/1.06  cnf(c_0_41, negated_conjecture, (k7_relat_1(k5_relat_1(esk1_0,esk2_0),X1)=k5_relat_1(k7_relat_1(esk1_0,X1),esk2_0)), inference(spm,[status(thm)],[c_0_33, c_0_24])).
% 0.84/1.06  fof(c_0_42, plain, ![X9, X10]:(~v1_relat_1(X9)|~v1_relat_1(X10)|v1_relat_1(k5_relat_1(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.84/1.06  cnf(c_0_43, negated_conjecture, (k1_relat_1(k7_relat_1(esk1_0,esk3_0))=esk3_0|r1_tarski(esk3_0,X1)|~r1_tarski(k1_relat_1(k5_relat_1(esk1_0,esk2_0)),X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.84/1.06  cnf(c_0_44, negated_conjecture, (r1_tarski(k1_relat_1(k5_relat_1(esk1_0,esk2_0)),k1_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_26])])).
% 0.84/1.06  cnf(c_0_45, plain, (k1_relat_1(k5_relat_1(X1,X2))=k1_relat_1(X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(k2_relat_1(X1),k1_relat_1(X2))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.84/1.06  cnf(c_0_46, negated_conjecture, (k2_relat_1(k7_relat_1(esk1_0,X1))=k9_relat_1(esk1_0,X1)), inference(spm,[status(thm)],[c_0_39, c_0_26])).
% 0.84/1.06  fof(c_0_47, plain, ![X11, X12]:(~v1_relat_1(X11)|v1_relat_1(k7_relat_1(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.84/1.06  cnf(c_0_48, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,k9_relat_1(esk1_0,esk3_0)))=k9_relat_1(esk1_0,esk3_0)|k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0))=esk3_0|~v1_relat_1(k5_relat_1(esk1_0,esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_40]), c_0_41])).
% 0.84/1.06  cnf(c_0_49, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.84/1.06  cnf(c_0_50, negated_conjecture, (k1_relat_1(k7_relat_1(esk1_0,esk3_0))=esk3_0|r1_tarski(esk3_0,k1_relat_1(esk1_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.84/1.06  cnf(c_0_51, negated_conjecture, (k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,X1),X2))=k1_relat_1(k7_relat_1(esk1_0,X1))|~v1_relat_1(k7_relat_1(esk1_0,X1))|~v1_relat_1(X2)|~r1_tarski(k9_relat_1(esk1_0,X1),k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.84/1.06  cnf(c_0_52, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.84/1.06  cnf(c_0_53, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,k9_relat_1(esk1_0,esk3_0)))=k9_relat_1(esk1_0,esk3_0)|k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_24]), c_0_26])])).
% 0.84/1.06  cnf(c_0_54, negated_conjecture, (k1_relat_1(k7_relat_1(esk1_0,esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_50]), c_0_26])])).
% 0.84/1.06  cnf(c_0_55, negated_conjecture, (r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,X1),esk2_0)),k1_relat_1(k5_relat_1(esk1_0,esk2_0)))|~v1_relat_1(k5_relat_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_36, c_0_41])).
% 0.84/1.06  cnf(c_0_56, negated_conjecture, (k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,X1),X2))=k1_relat_1(k7_relat_1(esk1_0,X1))|~v1_relat_1(X2)|~r1_tarski(k9_relat_1(esk1_0,X1),k1_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_26])])).
% 0.84/1.06  cnf(c_0_57, negated_conjecture, (k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0))=esk3_0|r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_53]), c_0_24])])).
% 0.84/1.06  cnf(c_0_58, negated_conjecture, (~r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))|~r1_tarski(esk3_0,k1_relat_1(esk1_0))|~r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.84/1.06  cnf(c_0_59, negated_conjecture, (r1_tarski(esk3_0,k1_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_54]), c_0_26])])).
% 0.84/1.06  cnf(c_0_60, negated_conjecture, (r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,X1),esk2_0)),k1_relat_1(k5_relat_1(esk1_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_49]), c_0_24]), c_0_26])])).
% 0.84/1.06  cnf(c_0_61, negated_conjecture, (k1_relat_1(k5_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_54]), c_0_24])])).
% 0.84/1.06  fof(c_0_62, plain, ![X28, X29]:(~v1_relat_1(X28)|~v1_funct_1(X28)|(~v1_relat_1(X29)|~v1_funct_1(X29)|(k1_relat_1(k5_relat_1(X29,X28))!=k1_relat_1(X29)|r1_tarski(k2_relat_1(X29),k1_relat_1(X28))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_funct_1])])])).
% 0.84/1.06  cnf(c_0_63, negated_conjecture, (~r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))|~r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59])])).
% 0.84/1.06  cnf(c_0_64, negated_conjecture, (r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.84/1.06  cnf(c_0_65, plain, (r1_tarski(k2_relat_1(X2),k1_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k1_relat_1(k5_relat_1(X2,X1))!=k1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.84/1.06  cnf(c_0_66, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.84/1.06  cnf(c_0_67, negated_conjecture, (~r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64])])).
% 0.84/1.06  fof(c_0_68, plain, ![X26, X27]:((v1_relat_1(k7_relat_1(X26,X27))|(~v1_relat_1(X26)|~v1_funct_1(X26)))&(v1_funct_1(k7_relat_1(X26,X27))|(~v1_relat_1(X26)|~v1_funct_1(X26)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).
% 0.84/1.06  cnf(c_0_69, negated_conjecture, (~v1_funct_1(k7_relat_1(esk1_0,esk3_0))|~v1_relat_1(k7_relat_1(esk1_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_61]), c_0_46]), c_0_54]), c_0_66]), c_0_24])]), c_0_67])).
% 0.84/1.06  cnf(c_0_70, plain, (v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.84/1.06  cnf(c_0_71, negated_conjecture, (v1_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.84/1.06  cnf(c_0_72, negated_conjecture, (~v1_relat_1(k7_relat_1(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71]), c_0_26])])).
% 0.84/1.06  cnf(c_0_73, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_52]), c_0_26])]), ['proof']).
% 0.84/1.06  # SZS output end CNFRefutation
% 0.84/1.06  # Proof object total steps             : 74
% 0.84/1.06  # Proof object clause steps            : 47
% 0.84/1.06  # Proof object formula steps           : 27
% 0.84/1.06  # Proof object conjectures             : 37
% 0.84/1.06  # Proof object clause conjectures      : 34
% 0.84/1.06  # Proof object formula conjectures     : 3
% 0.84/1.06  # Proof object initial clauses used    : 19
% 0.84/1.06  # Proof object initial formulas used   : 13
% 0.84/1.06  # Proof object generating inferences   : 26
% 0.84/1.06  # Proof object simplifying inferences  : 39
% 0.84/1.06  # Training examples: 0 positive, 0 negative
% 0.84/1.06  # Parsed axioms                        : 13
% 0.84/1.06  # Removed by relevancy pruning/SinE    : 0
% 0.84/1.06  # Initial clauses                      : 20
% 0.84/1.06  # Removed in clause preprocessing      : 0
% 0.84/1.06  # Initial clauses in saturation        : 20
% 0.84/1.06  # Processed clauses                    : 3518
% 0.84/1.06  # ...of these trivial                  : 291
% 0.84/1.06  # ...subsumed                          : 670
% 0.84/1.06  # ...remaining for further processing  : 2557
% 0.84/1.06  # Other redundant clauses eliminated   : 0
% 0.84/1.06  # Clauses deleted for lack of memory   : 0
% 0.84/1.06  # Backward-subsumed                    : 162
% 0.84/1.06  # Backward-rewritten                   : 61
% 0.84/1.06  # Generated clauses                    : 70156
% 0.84/1.06  # ...of the previous two non-trivial   : 69408
% 0.84/1.06  # Contextual simplify-reflections      : 1
% 0.84/1.06  # Paramodulations                      : 70156
% 0.84/1.06  # Factorizations                       : 0
% 0.84/1.06  # Equation resolutions                 : 0
% 0.84/1.06  # Propositional unsat checks           : 0
% 0.84/1.06  #    Propositional check models        : 0
% 0.84/1.06  #    Propositional check unsatisfiable : 0
% 0.84/1.06  #    Propositional clauses             : 0
% 0.84/1.06  #    Propositional clauses after purity: 0
% 0.84/1.06  #    Propositional unsat core size     : 0
% 0.84/1.06  #    Propositional preprocessing time  : 0.000
% 0.84/1.06  #    Propositional encoding time       : 0.000
% 0.84/1.06  #    Propositional solver time         : 0.000
% 0.84/1.06  #    Success case prop preproc time    : 0.000
% 0.84/1.06  #    Success case prop encoding time   : 0.000
% 0.84/1.06  #    Success case prop solver time     : 0.000
% 0.84/1.06  # Current number of processed clauses  : 2315
% 0.84/1.06  #    Positive orientable unit clauses  : 708
% 0.84/1.06  #    Positive unorientable unit clauses: 0
% 0.84/1.06  #    Negative unit clauses             : 2
% 0.84/1.06  #    Non-unit-clauses                  : 1605
% 0.84/1.06  # Current number of unprocessed clauses: 65904
% 0.84/1.06  # ...number of literals in the above   : 104075
% 0.84/1.06  # Current number of archived formulas  : 0
% 0.84/1.06  # Current number of archived clauses   : 242
% 0.84/1.06  # Clause-clause subsumption calls (NU) : 132733
% 0.84/1.06  # Rec. Clause-clause subsumption calls : 128636
% 0.84/1.06  # Non-unit clause-clause subsumptions  : 708
% 0.84/1.06  # Unit Clause-clause subsumption calls : 5731
% 0.84/1.06  # Rewrite failures with RHS unbound    : 0
% 0.84/1.06  # BW rewrite match attempts            : 43911
% 0.84/1.06  # BW rewrite match successes           : 106
% 0.84/1.06  # Condensation attempts                : 0
% 0.84/1.06  # Condensation successes               : 0
% 0.84/1.06  # Termbank termtop insertions          : 1761210
% 0.84/1.07  
% 0.84/1.07  # -------------------------------------------------
% 0.84/1.07  # User time                : 0.667 s
% 0.84/1.07  # System time              : 0.051 s
% 0.84/1.07  # Total time               : 0.718 s
% 0.84/1.07  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
