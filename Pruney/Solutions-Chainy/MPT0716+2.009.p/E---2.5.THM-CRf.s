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
% DateTime   : Thu Dec  3 10:55:44 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   65 (2400 expanded)
%              Number of clauses        :   50 ( 980 expanded)
%              Number of leaves         :    7 ( 553 expanded)
%              Depth                    :   26
%              Number of atoms          :  216 (12129 expanded)
%              Number of equality atoms :   13 ( 365 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
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

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(t163_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(X1,k1_relat_1(X3))
          & r1_tarski(k9_relat_1(X3,X1),X2) )
       => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t156_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

fof(c_0_7,negated_conjecture,(
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

fof(c_0_8,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X14)
      | ~ v1_relat_1(X15)
      | k1_relat_1(k5_relat_1(X14,X15)) = k10_relat_1(X14,k1_relat_1(X15)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

fof(c_0_9,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

cnf(c_0_10,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X26,X27,X28] :
      ( ~ v1_relat_1(X28)
      | ~ v1_funct_1(X28)
      | ~ r1_tarski(X26,k1_relat_1(X28))
      | ~ r1_tarski(k9_relat_1(X28,X26),X27)
      | r1_tarski(X26,k10_relat_1(X28,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).

fof(c_0_13,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_14,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk3_0,X1)) = k10_relat_1(esk3_0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r1_tarski(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))
    | r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk3_0,esk4_0)) = k10_relat_1(esk3_0,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( ~ r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))
    | ~ r1_tarski(esk5_0,k1_relat_1(esk3_0))
    | ~ r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_21,plain,(
    ! [X11,X12,X13] :
      ( ~ v1_relat_1(X13)
      | ~ r1_tarski(X11,X12)
      | r1_tarski(k9_relat_1(X13,X11),k9_relat_1(X13,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_2(X1,k1_relat_1(X2)),X1)
    | r1_tarski(X1,k10_relat_1(X2,X3))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k9_relat_1(X2,X1),X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))
    | r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),esk5_0)
    | ~ r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))
    | ~ r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_17])).

cnf(c_0_26,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),esk5_0)
    | r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_11])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),esk5_0)
    | ~ r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))
    | ~ r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_19])).

fof(c_0_29,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | ~ v1_funct_1(X25)
      | r1_tarski(k9_relat_1(X25,k10_relat_1(X25,X24)),X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

cnf(c_0_30,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),esk5_0)
    | r1_tarski(k9_relat_1(X1,esk5_0),k9_relat_1(X1,k10_relat_1(esk3_0,k1_relat_1(esk4_0))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),esk5_0)
    | ~ r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_33,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(X1,k9_relat_1(X2,k10_relat_1(esk3_0,k1_relat_1(esk4_0))))
    | r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),esk5_0)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k9_relat_1(X2,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk1_2(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)),k9_relat_1(esk3_0,esk5_0))
    | r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_17])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk5_0,k1_relat_1(esk3_0))
    | r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,k10_relat_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk1_2(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)),k9_relat_1(esk3_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0))))
    | r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_11])])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))
    | r1_tarski(esk5_0,k1_relat_1(esk3_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_36])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk1_2(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)),k1_relat_1(esk4_0))
    | r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_24]),c_0_11])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(X1,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))
    | r1_tarski(esk5_0,k1_relat_1(esk3_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(rw,[status(thm)],[c_0_39,c_0_19])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),k10_relat_1(esk3_0,k1_relat_1(esk4_0)))
    | r1_tarski(esk5_0,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),k10_relat_1(esk3_0,k1_relat_1(esk4_0)))
    | r1_tarski(esk5_0,k10_relat_1(esk3_0,X1))
    | ~ r1_tarski(k9_relat_1(esk3_0,esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_44]),c_0_24]),c_0_11])])).

fof(c_0_46,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22] :
      ( ( r2_hidden(X19,k1_relat_1(X16))
        | ~ r2_hidden(X19,X18)
        | X18 != k10_relat_1(X16,X17)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( r2_hidden(k1_funct_1(X16,X19),X17)
        | ~ r2_hidden(X19,X18)
        | X18 != k10_relat_1(X16,X17)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( ~ r2_hidden(X20,k1_relat_1(X16))
        | ~ r2_hidden(k1_funct_1(X16,X20),X17)
        | r2_hidden(X20,X18)
        | X18 != k10_relat_1(X16,X17)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( ~ r2_hidden(esk2_3(X16,X21,X22),X22)
        | ~ r2_hidden(esk2_3(X16,X21,X22),k1_relat_1(X16))
        | ~ r2_hidden(k1_funct_1(X16,esk2_3(X16,X21,X22)),X21)
        | X22 = k10_relat_1(X16,X21)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( r2_hidden(esk2_3(X16,X21,X22),k1_relat_1(X16))
        | r2_hidden(esk2_3(X16,X21,X22),X22)
        | X22 = k10_relat_1(X16,X21)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( r2_hidden(k1_funct_1(X16,esk2_3(X16,X21,X22)),X21)
        | r2_hidden(esk2_3(X16,X21,X22),X22)
        | X22 = k10_relat_1(X16,X21)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),k10_relat_1(esk3_0,k1_relat_1(esk4_0)))
    | r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_23])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,X3)
    | X3 != k10_relat_1(X2,X4)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),k10_relat_1(esk3_0,k1_relat_1(esk4_0)))
    | r2_hidden(X1,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_47])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k10_relat_1(X2,X3)) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),k10_relat_1(esk3_0,k1_relat_1(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_24]),c_0_11])])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk5_0,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_52])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk5_0,k10_relat_1(esk3_0,X1))
    | ~ r1_tarski(k9_relat_1(esk3_0,esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_53]),c_0_24]),c_0_11])])).

cnf(c_0_55,negated_conjecture,
    ( ~ r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))
    | ~ r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))
    | ~ r1_tarski(esk5_0,k1_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_23])).

cnf(c_0_57,negated_conjecture,
    ( ~ r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))
    | ~ r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_53])])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k9_relat_1(X1,esk5_0),k9_relat_1(X1,k10_relat_1(esk3_0,k1_relat_1(esk4_0))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_56])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(X1,k9_relat_1(X2,k10_relat_1(esk3_0,k1_relat_1(esk4_0))))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k9_relat_1(X2,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk1_2(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)),k9_relat_1(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_17])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk1_2(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)),k9_relat_1(esk3_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_11])])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk1_2(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_62]),c_0_24]),c_0_11])])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_63]),c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.35  % Computer   : n020.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % WCLimit    : 600
% 0.12/0.35  % DateTime   : Tue Dec  1 16:10:52 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.44  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.19/0.44  # and selection function SelectNewComplexAHP.
% 0.19/0.44  #
% 0.19/0.44  # Preprocessing time       : 0.043 s
% 0.19/0.44  # Presaturation interreduction done
% 0.19/0.44  
% 0.19/0.44  # Proof found!
% 0.19/0.44  # SZS status Theorem
% 0.19/0.44  # SZS output start CNFRefutation
% 0.19/0.44  fof(t171_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:(r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))<=>(r1_tarski(X3,k1_relat_1(X1))&r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_1)).
% 0.19/0.44  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 0.19/0.44  fof(t163_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(X1,k1_relat_1(X3))&r1_tarski(k9_relat_1(X3,X1),X2))=>r1_tarski(X1,k10_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 0.19/0.44  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.44  fof(t156_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 0.19/0.44  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 0.19/0.44  fof(d13_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,k1_relat_1(X1))&r2_hidden(k1_funct_1(X1,X4),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_funct_1)).
% 0.19/0.44  fof(c_0_7, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:(r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))<=>(r1_tarski(X3,k1_relat_1(X1))&r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2))))))), inference(assume_negation,[status(cth)],[t171_funct_1])).
% 0.19/0.44  fof(c_0_8, plain, ![X14, X15]:(~v1_relat_1(X14)|(~v1_relat_1(X15)|k1_relat_1(k5_relat_1(X14,X15))=k10_relat_1(X14,k1_relat_1(X15)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.19/0.44  fof(c_0_9, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&((~r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))|(~r1_tarski(esk5_0,k1_relat_1(esk3_0))|~r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))))&((r1_tarski(esk5_0,k1_relat_1(esk3_0))|r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0))))&(r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))|r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).
% 0.19/0.44  cnf(c_0_10, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.44  cnf(c_0_11, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.44  fof(c_0_12, plain, ![X26, X27, X28]:(~v1_relat_1(X28)|~v1_funct_1(X28)|(~r1_tarski(X26,k1_relat_1(X28))|~r1_tarski(k9_relat_1(X28,X26),X27)|r1_tarski(X26,k10_relat_1(X28,X27)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).
% 0.19/0.44  fof(c_0_13, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.44  cnf(c_0_14, negated_conjecture, (k1_relat_1(k5_relat_1(esk3_0,X1))=k10_relat_1(esk3_0,k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.19/0.44  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.44  cnf(c_0_16, plain, (r1_tarski(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~r1_tarski(k9_relat_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.44  cnf(c_0_17, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.44  cnf(c_0_18, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))|r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.44  cnf(c_0_19, negated_conjecture, (k1_relat_1(k5_relat_1(esk3_0,esk4_0))=k10_relat_1(esk3_0,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.44  cnf(c_0_20, negated_conjecture, (~r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))|~r1_tarski(esk5_0,k1_relat_1(esk3_0))|~r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.44  fof(c_0_21, plain, ![X11, X12, X13]:(~v1_relat_1(X13)|(~r1_tarski(X11,X12)|r1_tarski(k9_relat_1(X13,X11),k9_relat_1(X13,X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).
% 0.19/0.44  cnf(c_0_22, plain, (r2_hidden(esk1_2(X1,k1_relat_1(X2)),X1)|r1_tarski(X1,k10_relat_1(X2,X3))|~v1_funct_1(X2)|~v1_relat_1(X2)|~r1_tarski(k9_relat_1(X2,X1),X3)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.44  cnf(c_0_23, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))|r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.44  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.44  cnf(c_0_25, negated_conjecture, (r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),esk5_0)|~r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))|~r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_20, c_0_17])).
% 0.19/0.44  cnf(c_0_26, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.44  cnf(c_0_27, negated_conjecture, (r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),esk5_0)|r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_11])])).
% 0.19/0.44  cnf(c_0_28, negated_conjecture, (r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),esk5_0)|~r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))|~r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))), inference(rw,[status(thm)],[c_0_25, c_0_19])).
% 0.19/0.44  fof(c_0_29, plain, ![X24, X25]:(~v1_relat_1(X25)|~v1_funct_1(X25)|r1_tarski(k9_relat_1(X25,k10_relat_1(X25,X24)),X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.19/0.44  cnf(c_0_30, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.44  cnf(c_0_31, negated_conjecture, (r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),esk5_0)|r1_tarski(k9_relat_1(X1,esk5_0),k9_relat_1(X1,k10_relat_1(esk3_0,k1_relat_1(esk4_0))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.44  cnf(c_0_32, negated_conjecture, (r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),esk5_0)|~r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_28, c_0_27])).
% 0.19/0.44  cnf(c_0_33, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.44  cnf(c_0_34, negated_conjecture, (r2_hidden(X1,k9_relat_1(X2,k10_relat_1(esk3_0,k1_relat_1(esk4_0))))|r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),esk5_0)|~v1_relat_1(X2)|~r2_hidden(X1,k9_relat_1(X2,esk5_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.44  cnf(c_0_35, negated_conjecture, (r2_hidden(esk1_2(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)),k9_relat_1(esk3_0,esk5_0))|r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_17])).
% 0.19/0.44  cnf(c_0_36, negated_conjecture, (r1_tarski(esk5_0,k1_relat_1(esk3_0))|r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.44  cnf(c_0_37, plain, (r2_hidden(X1,X2)|~v1_funct_1(X3)|~v1_relat_1(X3)|~r2_hidden(X1,k9_relat_1(X3,k10_relat_1(X3,X2)))), inference(spm,[status(thm)],[c_0_30, c_0_33])).
% 0.19/0.44  cnf(c_0_38, negated_conjecture, (r2_hidden(esk1_2(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)),k9_relat_1(esk3_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0))))|r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_11])])).
% 0.19/0.44  cnf(c_0_39, negated_conjecture, (r2_hidden(X1,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))|r1_tarski(esk5_0,k1_relat_1(esk3_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_30, c_0_36])).
% 0.19/0.44  cnf(c_0_40, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.44  cnf(c_0_41, negated_conjecture, (r2_hidden(esk1_2(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)),k1_relat_1(esk4_0))|r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_24]), c_0_11])])).
% 0.19/0.44  cnf(c_0_42, negated_conjecture, (r2_hidden(X1,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))|r1_tarski(esk5_0,k1_relat_1(esk3_0))|~r2_hidden(X1,esk5_0)), inference(rw,[status(thm)],[c_0_39, c_0_19])).
% 0.19/0.44  cnf(c_0_43, negated_conjecture, (r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_32])).
% 0.19/0.44  cnf(c_0_44, negated_conjecture, (r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),k10_relat_1(esk3_0,k1_relat_1(esk4_0)))|r1_tarski(esk5_0,k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.44  cnf(c_0_45, negated_conjecture, (r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),k10_relat_1(esk3_0,k1_relat_1(esk4_0)))|r1_tarski(esk5_0,k10_relat_1(esk3_0,X1))|~r1_tarski(k9_relat_1(esk3_0,esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_44]), c_0_24]), c_0_11])])).
% 0.19/0.44  fof(c_0_46, plain, ![X16, X17, X18, X19, X20, X21, X22]:((((r2_hidden(X19,k1_relat_1(X16))|~r2_hidden(X19,X18)|X18!=k10_relat_1(X16,X17)|(~v1_relat_1(X16)|~v1_funct_1(X16)))&(r2_hidden(k1_funct_1(X16,X19),X17)|~r2_hidden(X19,X18)|X18!=k10_relat_1(X16,X17)|(~v1_relat_1(X16)|~v1_funct_1(X16))))&(~r2_hidden(X20,k1_relat_1(X16))|~r2_hidden(k1_funct_1(X16,X20),X17)|r2_hidden(X20,X18)|X18!=k10_relat_1(X16,X17)|(~v1_relat_1(X16)|~v1_funct_1(X16))))&((~r2_hidden(esk2_3(X16,X21,X22),X22)|(~r2_hidden(esk2_3(X16,X21,X22),k1_relat_1(X16))|~r2_hidden(k1_funct_1(X16,esk2_3(X16,X21,X22)),X21))|X22=k10_relat_1(X16,X21)|(~v1_relat_1(X16)|~v1_funct_1(X16)))&((r2_hidden(esk2_3(X16,X21,X22),k1_relat_1(X16))|r2_hidden(esk2_3(X16,X21,X22),X22)|X22=k10_relat_1(X16,X21)|(~v1_relat_1(X16)|~v1_funct_1(X16)))&(r2_hidden(k1_funct_1(X16,esk2_3(X16,X21,X22)),X21)|r2_hidden(esk2_3(X16,X21,X22),X22)|X22=k10_relat_1(X16,X21)|(~v1_relat_1(X16)|~v1_funct_1(X16)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).
% 0.19/0.44  cnf(c_0_47, negated_conjecture, (r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),k10_relat_1(esk3_0,k1_relat_1(esk4_0)))|r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))), inference(spm,[status(thm)],[c_0_45, c_0_23])).
% 0.19/0.44  cnf(c_0_48, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,X3)|X3!=k10_relat_1(X2,X4)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.44  cnf(c_0_49, negated_conjecture, (r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),k10_relat_1(esk3_0,k1_relat_1(esk4_0)))|r2_hidden(X1,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_30, c_0_47])).
% 0.19/0.44  cnf(c_0_50, plain, (r2_hidden(X1,k1_relat_1(X2))|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k10_relat_1(X2,X3))), inference(er,[status(thm)],[c_0_48])).
% 0.19/0.44  cnf(c_0_51, negated_conjecture, (r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),k10_relat_1(esk3_0,k1_relat_1(esk4_0)))), inference(spm,[status(thm)],[c_0_49, c_0_43])).
% 0.19/0.44  cnf(c_0_52, negated_conjecture, (r2_hidden(esk1_2(esk5_0,k1_relat_1(esk3_0)),k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_24]), c_0_11])])).
% 0.19/0.44  cnf(c_0_53, negated_conjecture, (r1_tarski(esk5_0,k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_40, c_0_52])).
% 0.19/0.44  cnf(c_0_54, negated_conjecture, (r1_tarski(esk5_0,k10_relat_1(esk3_0,X1))|~r1_tarski(k9_relat_1(esk3_0,esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_53]), c_0_24]), c_0_11])])).
% 0.19/0.44  cnf(c_0_55, negated_conjecture, (~r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))|~r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))|~r1_tarski(esk5_0,k1_relat_1(esk3_0))), inference(rw,[status(thm)],[c_0_20, c_0_19])).
% 0.19/0.44  cnf(c_0_56, negated_conjecture, (r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))), inference(spm,[status(thm)],[c_0_54, c_0_23])).
% 0.19/0.44  cnf(c_0_57, negated_conjecture, (~r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))|~r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_53])])).
% 0.19/0.44  cnf(c_0_58, negated_conjecture, (r1_tarski(k9_relat_1(X1,esk5_0),k9_relat_1(X1,k10_relat_1(esk3_0,k1_relat_1(esk4_0))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_26, c_0_56])).
% 0.19/0.44  cnf(c_0_59, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_56])])).
% 0.19/0.44  cnf(c_0_60, negated_conjecture, (r2_hidden(X1,k9_relat_1(X2,k10_relat_1(esk3_0,k1_relat_1(esk4_0))))|~v1_relat_1(X2)|~r2_hidden(X1,k9_relat_1(X2,esk5_0))), inference(spm,[status(thm)],[c_0_30, c_0_58])).
% 0.19/0.44  cnf(c_0_61, negated_conjecture, (r2_hidden(esk1_2(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)),k9_relat_1(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_59, c_0_17])).
% 0.19/0.44  cnf(c_0_62, negated_conjecture, (r2_hidden(esk1_2(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)),k9_relat_1(esk3_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_11])])).
% 0.19/0.44  cnf(c_0_63, negated_conjecture, (r2_hidden(esk1_2(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_62]), c_0_24]), c_0_11])])).
% 0.19/0.44  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_63]), c_0_59]), ['proof']).
% 0.19/0.44  # SZS output end CNFRefutation
% 0.19/0.44  # Proof object total steps             : 65
% 0.19/0.44  # Proof object clause steps            : 50
% 0.19/0.44  # Proof object formula steps           : 15
% 0.19/0.44  # Proof object conjectures             : 42
% 0.19/0.44  # Proof object clause conjectures      : 39
% 0.19/0.44  # Proof object formula conjectures     : 3
% 0.19/0.44  # Proof object initial clauses used    : 14
% 0.19/0.44  # Proof object initial formulas used   : 7
% 0.19/0.44  # Proof object generating inferences   : 29
% 0.19/0.44  # Proof object simplifying inferences  : 33
% 0.19/0.44  # Training examples: 0 positive, 0 negative
% 0.19/0.44  # Parsed axioms                        : 8
% 0.19/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.44  # Initial clauses                      : 23
% 0.19/0.44  # Removed in clause preprocessing      : 0
% 0.19/0.44  # Initial clauses in saturation        : 23
% 0.19/0.44  # Processed clauses                    : 255
% 0.19/0.44  # ...of these trivial                  : 2
% 0.19/0.44  # ...subsumed                          : 50
% 0.19/0.44  # ...remaining for further processing  : 203
% 0.19/0.44  # Other redundant clauses eliminated   : 3
% 0.19/0.44  # Clauses deleted for lack of memory   : 0
% 0.19/0.44  # Backward-subsumed                    : 13
% 0.19/0.44  # Backward-rewritten                   : 56
% 0.19/0.44  # Generated clauses                    : 726
% 0.19/0.44  # ...of the previous two non-trivial   : 718
% 0.19/0.44  # Contextual simplify-reflections      : 4
% 0.19/0.44  # Paramodulations                      : 717
% 0.19/0.44  # Factorizations                       : 6
% 0.19/0.44  # Equation resolutions                 : 3
% 0.19/0.44  # Propositional unsat checks           : 0
% 0.19/0.44  #    Propositional check models        : 0
% 0.19/0.44  #    Propositional check unsatisfiable : 0
% 0.19/0.44  #    Propositional clauses             : 0
% 0.19/0.44  #    Propositional clauses after purity: 0
% 0.19/0.44  #    Propositional unsat core size     : 0
% 0.19/0.44  #    Propositional preprocessing time  : 0.000
% 0.19/0.44  #    Propositional encoding time       : 0.000
% 0.19/0.44  #    Propositional solver time         : 0.000
% 0.19/0.44  #    Success case prop preproc time    : 0.000
% 0.19/0.44  #    Success case prop encoding time   : 0.000
% 0.19/0.44  #    Success case prop solver time     : 0.000
% 0.19/0.44  # Current number of processed clauses  : 108
% 0.19/0.44  #    Positive orientable unit clauses  : 23
% 0.19/0.44  #    Positive unorientable unit clauses: 0
% 0.19/0.44  #    Negative unit clauses             : 1
% 0.19/0.44  #    Non-unit-clauses                  : 84
% 0.19/0.44  # Current number of unprocessed clauses: 462
% 0.19/0.44  # ...number of literals in the above   : 1914
% 0.19/0.44  # Current number of archived formulas  : 0
% 0.19/0.44  # Current number of archived clauses   : 92
% 0.19/0.44  # Clause-clause subsumption calls (NU) : 1972
% 0.19/0.44  # Rec. Clause-clause subsumption calls : 734
% 0.19/0.44  # Non-unit clause-clause subsumptions  : 65
% 0.19/0.44  # Unit Clause-clause subsumption calls : 79
% 0.19/0.44  # Rewrite failures with RHS unbound    : 0
% 0.19/0.44  # BW rewrite match attempts            : 11
% 0.19/0.44  # BW rewrite match successes           : 6
% 0.19/0.44  # Condensation attempts                : 0
% 0.19/0.44  # Condensation successes               : 0
% 0.19/0.44  # Termbank termtop insertions          : 19699
% 0.19/0.44  
% 0.19/0.44  # -------------------------------------------------
% 0.19/0.44  # User time                : 0.080 s
% 0.19/0.44  # System time              : 0.012 s
% 0.19/0.44  # Total time               : 0.092 s
% 0.19/0.44  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
