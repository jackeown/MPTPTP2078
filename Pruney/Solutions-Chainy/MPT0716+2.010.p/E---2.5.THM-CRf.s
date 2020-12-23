%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:44 EST 2020

% Result     : Theorem 0.62s
% Output     : CNFRefutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 434 expanded)
%              Number of clauses        :   49 ( 176 expanded)
%              Number of leaves         :   12 ( 104 expanded)
%              Depth                    :   15
%              Number of atoms          :  205 (1974 expanded)
%              Number of equality atoms :   33 ( 106 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   11 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t112_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k7_relat_1(k5_relat_1(X2,X3),X1) = k5_relat_1(k7_relat_1(X2,X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

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

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t46_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
           => k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

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

fof(c_0_12,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X26)
      | ~ r1_tarski(X25,k1_relat_1(X26))
      | k1_relat_1(k7_relat_1(X26,X25)) = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

fof(c_0_13,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X19)
      | ~ v1_relat_1(X20)
      | r1_tarski(k1_relat_1(k5_relat_1(X19,X20)),k1_relat_1(X19)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_relat_1])])])).

fof(c_0_14,negated_conjecture,(
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

fof(c_0_15,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_16,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k1_relat_1(k7_relat_1(X1,k1_relat_1(k5_relat_1(X1,X2)))) = k1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))
    | r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X14,X15,X16] :
      ( ~ v1_relat_1(X15)
      | ~ v1_relat_1(X16)
      | k7_relat_1(k5_relat_1(X15,X16),X14) = k5_relat_1(k7_relat_1(X15,X14),X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_27,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X24)
      | r1_tarski(k1_relat_1(k7_relat_1(X24,X23)),k1_relat_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t89_relat_1])])).

cnf(c_0_28,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,k1_relat_1(k5_relat_1(esk2_0,X1)))) = k1_relat_1(k5_relat_1(esk2_0,X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_29,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X18)
      | k2_relat_1(k7_relat_1(X18,X17)) = k9_relat_1(X18,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_30,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk3_0,k9_relat_1(esk2_0,esk4_0))) = k9_relat_1(esk2_0,esk4_0)
    | r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_23]),c_0_24])])).

fof(c_0_31,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ v1_relat_1(X11)
      | v1_relat_1(k5_relat_1(X10,X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_32,plain,
    ( k7_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_tarski(X4,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(spm,[status(thm)],[c_0_26,c_0_20])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))) = k1_relat_1(k5_relat_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_24])).

fof(c_0_37,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X21)
      | ~ v1_relat_1(X22)
      | ~ r1_tarski(k2_relat_1(X21),k1_relat_1(X22))
      | k1_relat_1(k5_relat_1(X21,X22)) = k1_relat_1(X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_relat_1])])])).

cnf(c_0_38,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk3_0,k9_relat_1(esk2_0,esk4_0))) = k9_relat_1(esk2_0,esk4_0)
    | k1_relat_1(k7_relat_1(k5_relat_1(esk2_0,esk3_0),esk4_0)) = esk4_0
    | ~ v1_relat_1(k5_relat_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_30])).

cnf(c_0_40,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( k7_relat_1(k5_relat_1(esk2_0,X1),X2) = k5_relat_1(k7_relat_1(esk2_0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_22])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k1_relat_1(k5_relat_1(esk2_0,esk3_0)),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_22])])).

cnf(c_0_44,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk2_0,X1)) = k9_relat_1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_22])).

fof(c_0_46,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X12)
      | v1_relat_1(k7_relat_1(X12,X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_47,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk3_0,k9_relat_1(esk2_0,esk4_0))) = k9_relat_1(esk2_0,esk4_0)
    | k1_relat_1(k7_relat_1(k5_relat_1(esk2_0,esk3_0),esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_24]),c_0_22])])).

cnf(c_0_48,negated_conjecture,
    ( k7_relat_1(k5_relat_1(esk2_0,esk3_0),X1) = k5_relat_1(k7_relat_1(esk2_0,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_24])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(X1,k1_relat_1(esk2_0))
    | ~ r1_tarski(X1,k1_relat_1(k5_relat_1(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk4_0,k1_relat_1(esk2_0))
    | r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_51,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k7_relat_1(esk2_0,X1),X2)) = k1_relat_1(k7_relat_1(esk2_0,X1))
    | ~ v1_relat_1(k7_relat_1(esk2_0,X1))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k9_relat_1(esk2_0,X1),k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk3_0,k9_relat_1(esk2_0,esk4_0))) = k9_relat_1(esk2_0,esk4_0)
    | k1_relat_1(k5_relat_1(k7_relat_1(esk2_0,esk4_0),esk3_0)) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk4_0,k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(esk2_0,X1),esk3_0)),k1_relat_1(k5_relat_1(esk2_0,esk3_0)))
    | ~ v1_relat_1(k5_relat_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k7_relat_1(esk2_0,X1),X2)) = k1_relat_1(k7_relat_1(esk2_0,X1))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k9_relat_1(esk2_0,X1),k1_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_22])])).

cnf(c_0_57,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k7_relat_1(esk2_0,esk4_0),esk3_0)) = esk4_0
    | r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_53]),c_0_24])])).

cnf(c_0_58,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_54]),c_0_22])])).

cnf(c_0_59,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))
    | ~ r1_tarski(esk4_0,k1_relat_1(esk2_0))
    | ~ r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(esk2_0,X1),esk3_0)),k1_relat_1(k5_relat_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_40]),c_0_24]),c_0_22])])).

cnf(c_0_61,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k7_relat_1(esk2_0,esk4_0),esk3_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_24])])).

fof(c_0_62,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X29)
      | ~ v1_funct_1(X29)
      | ~ v1_relat_1(X30)
      | ~ v1_funct_1(X30)
      | k1_relat_1(k5_relat_1(X30,X29)) != k1_relat_1(X30)
      | r1_tarski(k2_relat_1(X30),k1_relat_1(X29)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_funct_1])])])).

cnf(c_0_63,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))
    | ~ r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_54])])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0))) ),
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
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_67,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64])])).

fof(c_0_68,plain,(
    ! [X27,X28] :
      ( ( v1_relat_1(k7_relat_1(X27,X28))
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( v1_funct_1(k7_relat_1(X27,X28))
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_funct_1(k7_relat_1(esk2_0,esk4_0))
    | ~ v1_relat_1(k7_relat_1(esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_61]),c_0_45]),c_0_58]),c_0_66]),c_0_24])]),c_0_67])).

cnf(c_0_70,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_72,negated_conjecture,
    ( ~ v1_relat_1(k7_relat_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_22])])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_52]),c_0_22])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n017.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 11:27:46 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.62/0.78  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S01BI
% 0.62/0.78  # and selection function PSelectMinOptimalNoXTypePred.
% 0.62/0.78  #
% 0.62/0.78  # Preprocessing time       : 0.028 s
% 0.62/0.78  # Presaturation interreduction done
% 0.62/0.78  
% 0.62/0.78  # Proof found!
% 0.62/0.78  # SZS status Theorem
% 0.62/0.78  # SZS output start CNFRefutation
% 0.62/0.78  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 0.62/0.78  fof(t44_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 0.62/0.78  fof(t171_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:(r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))<=>(r1_tarski(X3,k1_relat_1(X1))&r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_1)).
% 0.62/0.78  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.62/0.78  fof(t112_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k7_relat_1(k5_relat_1(X2,X3),X1)=k5_relat_1(k7_relat_1(X2,X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 0.62/0.78  fof(t89_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),k1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 0.62/0.78  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.62/0.78  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.62/0.78  fof(t46_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X1),k1_relat_1(X2))=>k1_relat_1(k5_relat_1(X1,X2))=k1_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 0.62/0.78  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.62/0.78  fof(t27_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(k5_relat_1(X2,X1))=k1_relat_1(X2)=>r1_tarski(k2_relat_1(X2),k1_relat_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_funct_1)).
% 0.62/0.78  fof(fc8_funct_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k7_relat_1(X1,X2))&v1_funct_1(k7_relat_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 0.62/0.78  fof(c_0_12, plain, ![X25, X26]:(~v1_relat_1(X26)|(~r1_tarski(X25,k1_relat_1(X26))|k1_relat_1(k7_relat_1(X26,X25))=X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 0.62/0.78  fof(c_0_13, plain, ![X19, X20]:(~v1_relat_1(X19)|(~v1_relat_1(X20)|r1_tarski(k1_relat_1(k5_relat_1(X19,X20)),k1_relat_1(X19)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_relat_1])])])).
% 0.62/0.78  fof(c_0_14, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:(r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))<=>(r1_tarski(X3,k1_relat_1(X1))&r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2))))))), inference(assume_negation,[status(cth)],[t171_funct_1])).
% 0.62/0.78  fof(c_0_15, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.62/0.78  cnf(c_0_16, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.62/0.78  cnf(c_0_17, plain, (r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.62/0.78  fof(c_0_18, negated_conjecture, ((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((~r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))|(~r1_tarski(esk4_0,k1_relat_1(esk2_0))|~r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))))&((r1_tarski(esk4_0,k1_relat_1(esk2_0))|r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0))))&(r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))|r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])).
% 0.62/0.78  cnf(c_0_19, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.62/0.78  cnf(c_0_20, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.62/0.78  cnf(c_0_21, plain, (k1_relat_1(k7_relat_1(X1,k1_relat_1(k5_relat_1(X1,X2))))=k1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.62/0.78  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.62/0.78  cnf(c_0_23, negated_conjecture, (r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))|r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.62/0.78  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.62/0.78  fof(c_0_25, plain, ![X14, X15, X16]:(~v1_relat_1(X15)|(~v1_relat_1(X16)|k7_relat_1(k5_relat_1(X15,X16),X14)=k5_relat_1(k7_relat_1(X15,X14),X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).
% 0.62/0.78  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.62/0.78  fof(c_0_27, plain, ![X23, X24]:(~v1_relat_1(X24)|r1_tarski(k1_relat_1(k7_relat_1(X24,X23)),k1_relat_1(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t89_relat_1])])).
% 0.62/0.78  cnf(c_0_28, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,k1_relat_1(k5_relat_1(esk2_0,X1))))=k1_relat_1(k5_relat_1(esk2_0,X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.62/0.78  fof(c_0_29, plain, ![X17, X18]:(~v1_relat_1(X18)|k2_relat_1(k7_relat_1(X18,X17))=k9_relat_1(X18,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.62/0.78  cnf(c_0_30, negated_conjecture, (k1_relat_1(k7_relat_1(esk3_0,k9_relat_1(esk2_0,esk4_0)))=k9_relat_1(esk2_0,esk4_0)|r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_23]), c_0_24])])).
% 0.62/0.78  fof(c_0_31, plain, ![X10, X11]:(~v1_relat_1(X10)|~v1_relat_1(X11)|v1_relat_1(k5_relat_1(X10,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.62/0.78  cnf(c_0_32, plain, (k7_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.62/0.78  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_tarski(X4,X2)|~r1_tarski(X3,X4)), inference(spm,[status(thm)],[c_0_26, c_0_20])).
% 0.62/0.78  cnf(c_0_34, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.62/0.78  cnf(c_0_35, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.62/0.78  cnf(c_0_36, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0))))=k1_relat_1(k5_relat_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_28, c_0_24])).
% 0.62/0.78  fof(c_0_37, plain, ![X21, X22]:(~v1_relat_1(X21)|(~v1_relat_1(X22)|(~r1_tarski(k2_relat_1(X21),k1_relat_1(X22))|k1_relat_1(k5_relat_1(X21,X22))=k1_relat_1(X21)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_relat_1])])])).
% 0.62/0.78  cnf(c_0_38, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.62/0.78  cnf(c_0_39, negated_conjecture, (k1_relat_1(k7_relat_1(esk3_0,k9_relat_1(esk2_0,esk4_0)))=k9_relat_1(esk2_0,esk4_0)|k1_relat_1(k7_relat_1(k5_relat_1(esk2_0,esk3_0),esk4_0))=esk4_0|~v1_relat_1(k5_relat_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_16, c_0_30])).
% 0.62/0.78  cnf(c_0_40, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.62/0.78  cnf(c_0_41, negated_conjecture, (k7_relat_1(k5_relat_1(esk2_0,X1),X2)=k5_relat_1(k7_relat_1(esk2_0,X2),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_32, c_0_22])).
% 0.62/0.78  cnf(c_0_42, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.62/0.78  cnf(c_0_43, negated_conjecture, (r1_tarski(k1_relat_1(k5_relat_1(esk2_0,esk3_0)),k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_22])])).
% 0.62/0.78  cnf(c_0_44, plain, (k1_relat_1(k5_relat_1(X1,X2))=k1_relat_1(X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(k2_relat_1(X1),k1_relat_1(X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.62/0.78  cnf(c_0_45, negated_conjecture, (k2_relat_1(k7_relat_1(esk2_0,X1))=k9_relat_1(esk2_0,X1)), inference(spm,[status(thm)],[c_0_38, c_0_22])).
% 0.62/0.78  fof(c_0_46, plain, ![X12, X13]:(~v1_relat_1(X12)|v1_relat_1(k7_relat_1(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.62/0.78  cnf(c_0_47, negated_conjecture, (k1_relat_1(k7_relat_1(esk3_0,k9_relat_1(esk2_0,esk4_0)))=k9_relat_1(esk2_0,esk4_0)|k1_relat_1(k7_relat_1(k5_relat_1(esk2_0,esk3_0),esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_24]), c_0_22])])).
% 0.62/0.78  cnf(c_0_48, negated_conjecture, (k7_relat_1(k5_relat_1(esk2_0,esk3_0),X1)=k5_relat_1(k7_relat_1(esk2_0,X1),esk3_0)), inference(spm,[status(thm)],[c_0_41, c_0_24])).
% 0.62/0.78  cnf(c_0_49, negated_conjecture, (r1_tarski(X1,k1_relat_1(esk2_0))|~r1_tarski(X1,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.62/0.78  cnf(c_0_50, negated_conjecture, (r1_tarski(esk4_0,k1_relat_1(esk2_0))|r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.62/0.78  cnf(c_0_51, negated_conjecture, (k1_relat_1(k5_relat_1(k7_relat_1(esk2_0,X1),X2))=k1_relat_1(k7_relat_1(esk2_0,X1))|~v1_relat_1(k7_relat_1(esk2_0,X1))|~v1_relat_1(X2)|~r1_tarski(k9_relat_1(esk2_0,X1),k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.62/0.78  cnf(c_0_52, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.62/0.78  cnf(c_0_53, negated_conjecture, (k1_relat_1(k7_relat_1(esk3_0,k9_relat_1(esk2_0,esk4_0)))=k9_relat_1(esk2_0,esk4_0)|k1_relat_1(k5_relat_1(k7_relat_1(esk2_0,esk4_0),esk3_0))=esk4_0), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 0.62/0.78  cnf(c_0_54, negated_conjecture, (r1_tarski(esk4_0,k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.62/0.78  cnf(c_0_55, negated_conjecture, (r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(esk2_0,X1),esk3_0)),k1_relat_1(k5_relat_1(esk2_0,esk3_0)))|~v1_relat_1(k5_relat_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_35, c_0_48])).
% 0.62/0.78  cnf(c_0_56, negated_conjecture, (k1_relat_1(k5_relat_1(k7_relat_1(esk2_0,X1),X2))=k1_relat_1(k7_relat_1(esk2_0,X1))|~v1_relat_1(X2)|~r1_tarski(k9_relat_1(esk2_0,X1),k1_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_22])])).
% 0.62/0.78  cnf(c_0_57, negated_conjecture, (k1_relat_1(k5_relat_1(k7_relat_1(esk2_0,esk4_0),esk3_0))=esk4_0|r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_53]), c_0_24])])).
% 0.62/0.78  cnf(c_0_58, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_54]), c_0_22])])).
% 0.62/0.78  cnf(c_0_59, negated_conjecture, (~r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))|~r1_tarski(esk4_0,k1_relat_1(esk2_0))|~r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.62/0.78  cnf(c_0_60, negated_conjecture, (r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(esk2_0,X1),esk3_0)),k1_relat_1(k5_relat_1(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_40]), c_0_24]), c_0_22])])).
% 0.62/0.78  cnf(c_0_61, negated_conjecture, (k1_relat_1(k5_relat_1(k7_relat_1(esk2_0,esk4_0),esk3_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), c_0_24])])).
% 0.62/0.78  fof(c_0_62, plain, ![X29, X30]:(~v1_relat_1(X29)|~v1_funct_1(X29)|(~v1_relat_1(X30)|~v1_funct_1(X30)|(k1_relat_1(k5_relat_1(X30,X29))!=k1_relat_1(X30)|r1_tarski(k2_relat_1(X30),k1_relat_1(X29))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_funct_1])])])).
% 0.62/0.78  cnf(c_0_63, negated_conjecture, (~r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))|~r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_54])])).
% 0.62/0.78  cnf(c_0_64, negated_conjecture, (r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.62/0.78  cnf(c_0_65, plain, (r1_tarski(k2_relat_1(X2),k1_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k1_relat_1(k5_relat_1(X2,X1))!=k1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.62/0.78  cnf(c_0_66, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.62/0.78  cnf(c_0_67, negated_conjecture, (~r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64])])).
% 0.62/0.78  fof(c_0_68, plain, ![X27, X28]:((v1_relat_1(k7_relat_1(X27,X28))|(~v1_relat_1(X27)|~v1_funct_1(X27)))&(v1_funct_1(k7_relat_1(X27,X28))|(~v1_relat_1(X27)|~v1_funct_1(X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).
% 0.62/0.78  cnf(c_0_69, negated_conjecture, (~v1_funct_1(k7_relat_1(esk2_0,esk4_0))|~v1_relat_1(k7_relat_1(esk2_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_61]), c_0_45]), c_0_58]), c_0_66]), c_0_24])]), c_0_67])).
% 0.62/0.78  cnf(c_0_70, plain, (v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.62/0.78  cnf(c_0_71, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.62/0.78  cnf(c_0_72, negated_conjecture, (~v1_relat_1(k7_relat_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71]), c_0_22])])).
% 0.62/0.78  cnf(c_0_73, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_52]), c_0_22])]), ['proof']).
% 0.62/0.78  # SZS output end CNFRefutation
% 0.62/0.78  # Proof object total steps             : 74
% 0.62/0.78  # Proof object clause steps            : 49
% 0.62/0.78  # Proof object formula steps           : 25
% 0.62/0.78  # Proof object conjectures             : 35
% 0.62/0.78  # Proof object clause conjectures      : 32
% 0.62/0.78  # Proof object formula conjectures     : 3
% 0.62/0.78  # Proof object initial clauses used    : 20
% 0.62/0.78  # Proof object initial formulas used   : 12
% 0.62/0.78  # Proof object generating inferences   : 26
% 0.62/0.78  # Proof object simplifying inferences  : 35
% 0.62/0.78  # Training examples: 0 positive, 0 negative
% 0.62/0.78  # Parsed axioms                        : 12
% 0.62/0.78  # Removed by relevancy pruning/SinE    : 0
% 0.62/0.78  # Initial clauses                      : 21
% 0.62/0.78  # Removed in clause preprocessing      : 0
% 0.62/0.78  # Initial clauses in saturation        : 21
% 0.62/0.78  # Processed clauses                    : 2516
% 0.62/0.78  # ...of these trivial                  : 60
% 0.62/0.78  # ...subsumed                          : 1091
% 0.62/0.78  # ...remaining for further processing  : 1365
% 0.62/0.78  # Other redundant clauses eliminated   : 0
% 0.62/0.78  # Clauses deleted for lack of memory   : 0
% 0.62/0.78  # Backward-subsumed                    : 272
% 0.62/0.78  # Backward-rewritten                   : 43
% 0.62/0.78  # Generated clauses                    : 13492
% 0.62/0.78  # ...of the previous two non-trivial   : 13155
% 0.62/0.78  # Contextual simplify-reflections      : 0
% 0.62/0.78  # Paramodulations                      : 13492
% 0.62/0.78  # Factorizations                       : 0
% 0.62/0.78  # Equation resolutions                 : 0
% 0.62/0.78  # Propositional unsat checks           : 0
% 0.62/0.78  #    Propositional check models        : 0
% 0.62/0.78  #    Propositional check unsatisfiable : 0
% 0.62/0.78  #    Propositional clauses             : 0
% 0.62/0.78  #    Propositional clauses after purity: 0
% 0.62/0.78  #    Propositional unsat core size     : 0
% 0.62/0.78  #    Propositional preprocessing time  : 0.000
% 0.62/0.78  #    Propositional encoding time       : 0.000
% 0.62/0.78  #    Propositional solver time         : 0.000
% 0.62/0.78  #    Success case prop preproc time    : 0.000
% 0.62/0.78  #    Success case prop encoding time   : 0.000
% 0.62/0.78  #    Success case prop solver time     : 0.000
% 0.62/0.78  # Current number of processed clauses  : 1030
% 0.62/0.78  #    Positive orientable unit clauses  : 207
% 0.62/0.78  #    Positive unorientable unit clauses: 0
% 0.62/0.78  #    Negative unit clauses             : 16
% 0.62/0.78  #    Non-unit-clauses                  : 807
% 0.62/0.78  # Current number of unprocessed clauses: 10532
% 0.62/0.78  # ...number of literals in the above   : 27986
% 0.62/0.78  # Current number of archived formulas  : 0
% 0.62/0.78  # Current number of archived clauses   : 335
% 0.62/0.78  # Clause-clause subsumption calls (NU) : 156667
% 0.62/0.78  # Rec. Clause-clause subsumption calls : 31628
% 0.62/0.78  # Non-unit clause-clause subsumptions  : 1239
% 0.62/0.78  # Unit Clause-clause subsumption calls : 6488
% 0.62/0.78  # Rewrite failures with RHS unbound    : 0
% 0.62/0.78  # BW rewrite match attempts            : 2070
% 0.62/0.78  # BW rewrite match successes           : 52
% 0.62/0.78  # Condensation attempts                : 0
% 0.62/0.78  # Condensation successes               : 0
% 0.62/0.78  # Termbank termtop insertions          : 353839
% 0.62/0.78  
% 0.62/0.78  # -------------------------------------------------
% 0.62/0.78  # User time                : 0.430 s
% 0.62/0.78  # System time              : 0.015 s
% 0.62/0.78  # Total time               : 0.445 s
% 0.62/0.78  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
