%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : ordinal1__t36_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:26 EDT 2019

% Result     : Theorem 0.55s
% Output     : CNFRefutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 193 expanded)
%              Number of clauses        :   36 (  87 expanded)
%              Number of leaves         :    9 (  48 expanded)
%              Depth                    :   18
%              Number of atoms          :  190 ( 642 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_ordinal1,conjecture,(
    ! [X1] :
      ~ ( ! [X2] :
            ( r2_hidden(X2,X1)
           => v3_ordinal1(X2) )
        & ! [X2] :
            ( v3_ordinal1(X2)
           => ~ r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t36_ordinal1.p',t36_ordinal1)).

fof(t35_ordinal1,axiom,(
    ! [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
         => v3_ordinal1(X2) )
     => v3_ordinal1(k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t36_ordinal1.p',t35_ordinal1)).

fof(connectedness_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
        | r1_ordinal1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t36_ordinal1.p',connectedness_r1_ordinal1)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t36_ordinal1.p',antisymmetry_r2_hidden)).

fof(t34_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,k1_ordinal1(X2))
          <=> r1_ordinal1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t36_ordinal1.p',t34_ordinal1)).

fof(fc2_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( ~ v1_xboole_0(k1_ordinal1(X1))
        & v3_ordinal1(k1_ordinal1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t36_ordinal1.p',fc2_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t36_ordinal1.p',redefinition_r1_ordinal1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t36_ordinal1.p',d3_tarski)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t36_ordinal1.p',d4_tarski)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ~ ( ! [X2] :
              ( r2_hidden(X2,X1)
             => v3_ordinal1(X2) )
          & ! [X2] :
              ( v3_ordinal1(X2)
             => ~ r1_tarski(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t36_ordinal1])).

fof(c_0_10,plain,(
    ! [X45] :
      ( ( r2_hidden(esk7_1(X45),X45)
        | v3_ordinal1(k3_tarski(X45)) )
      & ( ~ v3_ordinal1(esk7_1(X45))
        | v3_ordinal1(k3_tarski(X45)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_ordinal1])])])])).

fof(c_0_11,negated_conjecture,(
    ! [X6,X7] :
      ( ( ~ r2_hidden(X6,esk1_0)
        | v3_ordinal1(X6) )
      & ( ~ v3_ordinal1(X7)
        | ~ r1_tarski(esk1_0,X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])).

cnf(c_0_12,plain,
    ( v3_ordinal1(k3_tarski(X1))
    | ~ v3_ordinal1(esk7_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X12,X13] :
      ( ~ v3_ordinal1(X12)
      | ~ v3_ordinal1(X13)
      | r1_ordinal1(X12,X13)
      | r1_ordinal1(X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).

cnf(c_0_15,negated_conjecture,
    ( v3_ordinal1(k3_tarski(X1))
    | ~ r2_hidden(esk7_1(X1),esk1_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,plain,
    ( r2_hidden(esk7_1(X1),X1)
    | v3_ordinal1(k3_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X8,X9)
      | ~ r2_hidden(X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

fof(c_0_18,plain,(
    ! [X43,X44] :
      ( ( ~ r2_hidden(X43,k1_ordinal1(X44))
        | r1_ordinal1(X43,X44)
        | ~ v3_ordinal1(X44)
        | ~ v3_ordinal1(X43) )
      & ( ~ r1_ordinal1(X43,X44)
        | r2_hidden(X43,k1_ordinal1(X44))
        | ~ v3_ordinal1(X44)
        | ~ v3_ordinal1(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).

cnf(c_0_19,plain,
    ( r1_ordinal1(X1,X2)
    | r1_ordinal1(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v3_ordinal1(k3_tarski(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_21,plain,(
    ! [X60] :
      ( ( ~ v1_xboole_0(k1_ordinal1(X60))
        | ~ v3_ordinal1(X60) )
      & ( v3_ordinal1(k1_ordinal1(X60))
        | ~ v3_ordinal1(X60) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_ordinal1])])])])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r1_ordinal1(X1,k3_tarski(esk1_0))
    | r1_ordinal1(k3_tarski(esk1_0),X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(k1_ordinal1(X2),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( r1_ordinal1(k3_tarski(esk1_0),k1_ordinal1(X1))
    | r1_ordinal1(k1_ordinal1(X1),k3_tarski(esk1_0))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_28,plain,(
    ! [X34,X35] :
      ( ( ~ r1_ordinal1(X34,X35)
        | r1_tarski(X34,X35)
        | ~ v3_ordinal1(X34)
        | ~ v3_ordinal1(X35) )
      & ( ~ r1_tarski(X34,X35)
        | r1_ordinal1(X34,X35)
        | ~ v3_ordinal1(X34)
        | ~ v3_ordinal1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_29,plain,
    ( ~ r1_ordinal1(k1_ordinal1(X1),X2)
    | ~ r1_ordinal1(k1_ordinal1(X2),X1)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_23]),c_0_25]),c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r1_ordinal1(k1_ordinal1(k3_tarski(esk1_0)),k3_tarski(esk1_0))
    | r1_ordinal1(k3_tarski(esk1_0),k1_ordinal1(k3_tarski(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_20])).

fof(c_0_31,plain,(
    ! [X14,X15,X16,X17,X18] :
      ( ( ~ r1_tarski(X14,X15)
        | ~ r2_hidden(X16,X14)
        | r2_hidden(X16,X15) )
      & ( r2_hidden(esk2_2(X17,X18),X17)
        | r1_tarski(X17,X18) )
      & ( ~ r2_hidden(esk2_2(X17,X18),X18)
        | r1_tarski(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r1_ordinal1(k3_tarski(esk1_0),k1_ordinal1(k3_tarski(esk1_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_20])]),c_0_30])).

fof(c_0_34,plain,(
    ! [X20,X21,X22,X24,X25,X26,X27,X29] :
      ( ( r2_hidden(X22,esk3_3(X20,X21,X22))
        | ~ r2_hidden(X22,X21)
        | X21 != k3_tarski(X20) )
      & ( r2_hidden(esk3_3(X20,X21,X22),X20)
        | ~ r2_hidden(X22,X21)
        | X21 != k3_tarski(X20) )
      & ( ~ r2_hidden(X24,X25)
        | ~ r2_hidden(X25,X20)
        | r2_hidden(X24,X21)
        | X21 != k3_tarski(X20) )
      & ( ~ r2_hidden(esk4_2(X26,X27),X27)
        | ~ r2_hidden(esk4_2(X26,X27),X29)
        | ~ r2_hidden(X29,X26)
        | X27 = k3_tarski(X26) )
      & ( r2_hidden(esk4_2(X26,X27),esk5_2(X26,X27))
        | r2_hidden(esk4_2(X26,X27),X27)
        | X27 = k3_tarski(X26) )
      & ( r2_hidden(esk5_2(X26,X27),X26)
        | r2_hidden(esk4_2(X26,X27),X27)
        | X27 = k3_tarski(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_35,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k3_tarski(esk1_0),k1_ordinal1(k3_tarski(esk1_0)))
    | ~ v3_ordinal1(k1_ordinal1(k3_tarski(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_20])])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(X1,k1_ordinal1(k3_tarski(esk1_0)))
    | ~ v3_ordinal1(k1_ordinal1(k3_tarski(esk1_0)))
    | ~ r2_hidden(X1,k3_tarski(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_40,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(X1,k1_ordinal1(k3_tarski(esk1_0)))
    | ~ r2_hidden(X1,k3_tarski(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_25]),c_0_20])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | r2_hidden(X3,k3_tarski(X1))
    | ~ r2_hidden(X3,esk2_2(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,k1_ordinal1(X2))
    | ~ r1_ordinal1(esk2_2(X1,k1_ordinal1(X2)),X2)
    | ~ v3_ordinal1(esk2_2(X1,k1_ordinal1(X2)))
    | ~ v3_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_23])).

cnf(c_0_45,plain,
    ( r1_ordinal1(X1,X2)
    | ~ r1_tarski(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(X1,k1_ordinal1(k3_tarski(esk1_0)))
    | ~ r2_hidden(esk2_2(X1,k1_ordinal1(k3_tarski(esk1_0))),k3_tarski(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( r1_tarski(esk2_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | r2_hidden(esk2_2(esk2_2(X1,X2),X3),k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_40])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,k1_ordinal1(X2))
    | ~ r1_tarski(esk2_2(X1,k1_ordinal1(X2)),X2)
    | ~ v3_ordinal1(esk2_2(X1,k1_ordinal1(X2)))
    | ~ v3_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk2_2(esk1_0,X1),k1_ordinal1(k3_tarski(esk1_0)))
    | r1_tarski(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk1_0,k1_ordinal1(k1_ordinal1(k3_tarski(esk1_0))))
    | ~ v3_ordinal1(esk2_2(esk1_0,k1_ordinal1(k1_ordinal1(k3_tarski(esk1_0)))))
    | ~ v3_ordinal1(k1_ordinal1(k3_tarski(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_51,negated_conjecture,
    ( ~ v3_ordinal1(X1)
    | ~ r1_tarski(esk1_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk1_0,k1_ordinal1(k1_ordinal1(k3_tarski(esk1_0))))
    | ~ v3_ordinal1(k1_ordinal1(k3_tarski(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_13]),c_0_40])).

cnf(c_0_53,negated_conjecture,
    ( ~ v3_ordinal1(k1_ordinal1(k3_tarski(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_25])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_25]),c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
