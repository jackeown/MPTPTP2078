%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : wellord1__t37_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:13 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 542 expanded)
%              Number of clauses        :   46 ( 215 expanded)
%              Number of leaves         :    8 ( 127 expanded)
%              Depth                    :   18
%              Number of atoms          :  298 (3277 expanded)
%              Number of equality atoms :   43 ( 342 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t37_wellord1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( v2_wellord1(X3)
          & r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) )
       => ( r2_hidden(k4_tarski(X1,X2),X3)
        <=> r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t37_wellord1.p',t37_wellord1)).

fof(d4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
      <=> ( v1_relat_2(X1)
          & v8_relat_2(X1)
          & v4_relat_2(X1)
          & v6_relat_2(X1)
          & v1_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t37_wellord1.p',d4_wellord1)).

fof(l4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v6_relat_2(X1)
      <=> ! [X2,X3] :
            ~ ( r2_hidden(X2,k3_relat_1(X1))
              & r2_hidden(X3,k3_relat_1(X1))
              & X2 != X3
              & ~ r2_hidden(k4_tarski(X2,X3),X1)
              & ~ r2_hidden(k4_tarski(X3,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t37_wellord1.p',l4_wellord1)).

fof(d1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k1_wellord1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( X4 != X2
                & r2_hidden(k4_tarski(X4,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t37_wellord1.p',d1_wellord1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t37_wellord1.p',d3_tarski)).

fof(l2_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v8_relat_2(X1)
      <=> ! [X2,X3,X4] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
              & r2_hidden(k4_tarski(X3,X4),X1) )
           => r2_hidden(k4_tarski(X2,X4),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t37_wellord1.p',l2_wellord1)).

fof(l3_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_2(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
              & r2_hidden(k4_tarski(X3,X2),X1) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t37_wellord1.p',l3_wellord1)).

fof(l1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
      <=> ! [X2] :
            ( r2_hidden(X2,k3_relat_1(X1))
           => r2_hidden(k4_tarski(X2,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t37_wellord1.p',l1_wellord1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( ( v2_wellord1(X3)
            & r2_hidden(X1,k3_relat_1(X3))
            & r2_hidden(X2,k3_relat_1(X3)) )
         => ( r2_hidden(k4_tarski(X1,X2),X3)
          <=> r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t37_wellord1])).

fof(c_0_9,plain,(
    ! [X26] :
      ( ( v1_relat_2(X26)
        | ~ v2_wellord1(X26)
        | ~ v1_relat_1(X26) )
      & ( v8_relat_2(X26)
        | ~ v2_wellord1(X26)
        | ~ v1_relat_1(X26) )
      & ( v4_relat_2(X26)
        | ~ v2_wellord1(X26)
        | ~ v1_relat_1(X26) )
      & ( v6_relat_2(X26)
        | ~ v2_wellord1(X26)
        | ~ v1_relat_1(X26) )
      & ( v1_wellord1(X26)
        | ~ v2_wellord1(X26)
        | ~ v1_relat_1(X26) )
      & ( ~ v1_relat_2(X26)
        | ~ v8_relat_2(X26)
        | ~ v4_relat_2(X26)
        | ~ v6_relat_2(X26)
        | ~ v1_wellord1(X26)
        | v2_wellord1(X26)
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v2_wellord1(esk3_0)
    & r2_hidden(esk1_0,k3_relat_1(esk3_0))
    & r2_hidden(esk2_0,k3_relat_1(esk3_0))
    & ( ~ r2_hidden(k4_tarski(esk1_0,esk2_0),esk3_0)
      | ~ r1_tarski(k1_wellord1(esk3_0,esk1_0),k1_wellord1(esk3_0,esk2_0)) )
    & ( r2_hidden(k4_tarski(esk1_0,esk2_0),esk3_0)
      | r1_tarski(k1_wellord1(esk3_0,esk1_0),k1_wellord1(esk3_0,esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X45,X46,X47] :
      ( ( ~ v6_relat_2(X45)
        | ~ r2_hidden(X46,k3_relat_1(X45))
        | ~ r2_hidden(X47,k3_relat_1(X45))
        | X46 = X47
        | r2_hidden(k4_tarski(X46,X47),X45)
        | r2_hidden(k4_tarski(X47,X46),X45)
        | ~ v1_relat_1(X45) )
      & ( r2_hidden(esk13_1(X45),k3_relat_1(X45))
        | v6_relat_2(X45)
        | ~ v1_relat_1(X45) )
      & ( r2_hidden(esk14_1(X45),k3_relat_1(X45))
        | v6_relat_2(X45)
        | ~ v1_relat_1(X45) )
      & ( esk13_1(X45) != esk14_1(X45)
        | v6_relat_2(X45)
        | ~ v1_relat_1(X45) )
      & ( ~ r2_hidden(k4_tarski(esk13_1(X45),esk14_1(X45)),X45)
        | v6_relat_2(X45)
        | ~ v1_relat_1(X45) )
      & ( ~ r2_hidden(k4_tarski(esk14_1(X45),esk13_1(X45)),X45)
        | v6_relat_2(X45)
        | ~ v1_relat_1(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).

cnf(c_0_12,plain,
    ( v6_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( v2_wellord1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18] :
      ( ( X15 != X13
        | ~ r2_hidden(X15,X14)
        | X14 != k1_wellord1(X12,X13)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(k4_tarski(X15,X13),X12)
        | ~ r2_hidden(X15,X14)
        | X14 != k1_wellord1(X12,X13)
        | ~ v1_relat_1(X12) )
      & ( X16 = X13
        | ~ r2_hidden(k4_tarski(X16,X13),X12)
        | r2_hidden(X16,X14)
        | X14 != k1_wellord1(X12,X13)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(esk4_3(X12,X17,X18),X18)
        | esk4_3(X12,X17,X18) = X17
        | ~ r2_hidden(k4_tarski(esk4_3(X12,X17,X18),X17),X12)
        | X18 = k1_wellord1(X12,X17)
        | ~ v1_relat_1(X12) )
      & ( esk4_3(X12,X17,X18) != X17
        | r2_hidden(esk4_3(X12,X17,X18),X18)
        | X18 = k1_wellord1(X12,X17)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(k4_tarski(esk4_3(X12,X17,X18),X17),X12)
        | r2_hidden(esk4_3(X12,X17,X18),X18)
        | X18 = k1_wellord1(X12,X17)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).

cnf(c_0_16,plain,
    ( X2 = X3
    | r2_hidden(k4_tarski(X2,X3),X1)
    | r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v6_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(X3,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk2_0,k3_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( v6_relat_2(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])])).

fof(c_0_19,plain,(
    ! [X20,X21,X22,X23,X24] :
      ( ( ~ r1_tarski(X20,X21)
        | ~ r2_hidden(X22,X20)
        | r2_hidden(X22,X21) )
      & ( r2_hidden(esk5_2(X23,X24),X23)
        | r1_tarski(X23,X24) )
      & ( ~ r2_hidden(esk5_2(X23,X24),X24)
        | r1_tarski(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_20,plain,
    ( X1 = X2
    | r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( X1 = esk2_0
    | r2_hidden(k4_tarski(X1,esk2_0),esk3_0)
    | r2_hidden(k4_tarski(esk2_0,X1),esk3_0)
    | ~ r2_hidden(X1,k3_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_14])]),c_0_18])])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk1_0,k3_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_0,esk2_0),esk3_0)
    | r1_tarski(k1_wellord1(esk3_0,esk1_0),k1_wellord1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,plain,
    ( X1 = X2
    | r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( esk2_0 = esk1_0
    | r2_hidden(k4_tarski(esk2_0,esk1_0),esk3_0)
    | r2_hidden(k4_tarski(esk1_0,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,X3)
    | X3 != k1_wellord1(X4,X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_0,esk2_0),esk3_0)
    | r2_hidden(X1,k1_wellord1(esk3_0,esk2_0))
    | ~ r2_hidden(X1,k1_wellord1(esk3_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( esk2_0 = esk1_0
    | r2_hidden(k4_tarski(esk1_0,esk2_0),esk3_0)
    | r2_hidden(esk2_0,k1_wellord1(esk3_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_14])])).

fof(c_0_30,plain,(
    ! [X33,X34,X35,X36] :
      ( ( ~ v8_relat_2(X33)
        | ~ r2_hidden(k4_tarski(X34,X35),X33)
        | ~ r2_hidden(k4_tarski(X35,X36),X33)
        | r2_hidden(k4_tarski(X34,X36),X33)
        | ~ v1_relat_1(X33) )
      & ( r2_hidden(k4_tarski(esk8_1(X33),esk9_1(X33)),X33)
        | v8_relat_2(X33)
        | ~ v1_relat_1(X33) )
      & ( r2_hidden(k4_tarski(esk9_1(X33),esk10_1(X33)),X33)
        | v8_relat_2(X33)
        | ~ v1_relat_1(X33) )
      & ( ~ r2_hidden(k4_tarski(esk8_1(X33),esk10_1(X33)),X33)
        | v8_relat_2(X33)
        | ~ v1_relat_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l2_wellord1])])])])])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,k1_wellord1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_27])])).

cnf(c_0_32,negated_conjecture,
    ( esk2_0 = esk1_0
    | r2_hidden(esk2_0,k1_wellord1(esk3_0,esk2_0))
    | r2_hidden(k4_tarski(esk1_0,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(X2,X4),X1)
    | ~ v8_relat_2(X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X1)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( esk2_0 = esk1_0
    | r2_hidden(k4_tarski(esk1_0,esk2_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_14])])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_37,plain,
    ( r2_hidden(esk5_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_38,negated_conjecture,
    ( esk2_0 = esk1_0
    | r2_hidden(k4_tarski(X1,esk2_0),esk3_0)
    | ~ v8_relat_2(esk3_0)
    | ~ r2_hidden(k4_tarski(X1,esk1_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_14])])).

cnf(c_0_39,plain,
    ( v8_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_40,plain,
    ( r1_tarski(k1_wellord1(X1,X2),X3)
    | r2_hidden(k4_tarski(esk5_2(k1_wellord1(X1,X2),X3),X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( esk2_0 = esk1_0
    | r2_hidden(k4_tarski(X1,esk2_0),esk3_0)
    | ~ r2_hidden(k4_tarski(X1,esk1_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_13]),c_0_14])])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k1_wellord1(esk3_0,X1),X2)
    | r2_hidden(k4_tarski(esk5_2(k1_wellord1(esk3_0,X1),X2),X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_14])).

cnf(c_0_43,negated_conjecture,
    ( esk2_0 = esk1_0
    | r1_tarski(k1_wellord1(esk3_0,esk1_0),X1)
    | r2_hidden(k4_tarski(esk5_2(k1_wellord1(esk3_0,esk1_0),X1),esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk5_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_45,negated_conjecture,
    ( esk5_2(k1_wellord1(esk3_0,esk1_0),X1) = esk2_0
    | esk2_0 = esk1_0
    | r1_tarski(k1_wellord1(esk3_0,esk1_0),X1)
    | r2_hidden(esk5_2(k1_wellord1(esk3_0,esk1_0),X1),k1_wellord1(esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_43]),c_0_14])])).

fof(c_0_46,plain,(
    ! [X40,X41,X42] :
      ( ( ~ v4_relat_2(X40)
        | ~ r2_hidden(k4_tarski(X41,X42),X40)
        | ~ r2_hidden(k4_tarski(X42,X41),X40)
        | X41 = X42
        | ~ v1_relat_1(X40) )
      & ( r2_hidden(k4_tarski(esk11_1(X40),esk12_1(X40)),X40)
        | v4_relat_2(X40)
        | ~ v1_relat_1(X40) )
      & ( r2_hidden(k4_tarski(esk12_1(X40),esk11_1(X40)),X40)
        | v4_relat_2(X40)
        | ~ v1_relat_1(X40) )
      & ( esk11_1(X40) != esk12_1(X40)
        | v4_relat_2(X40)
        | ~ v1_relat_1(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_wellord1])])])])])).

cnf(c_0_47,negated_conjecture,
    ( esk5_2(k1_wellord1(esk3_0,esk1_0),k1_wellord1(esk3_0,esk2_0)) = esk2_0
    | esk2_0 = esk1_0
    | r1_tarski(k1_wellord1(esk3_0,esk1_0),k1_wellord1(esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_48,plain,
    ( X2 = X3
    | ~ v4_relat_2(X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X1)
    | ~ r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_49,plain,(
    ! [X30,X31] :
      ( ( ~ v1_relat_2(X30)
        | ~ r2_hidden(X31,k3_relat_1(X30))
        | r2_hidden(k4_tarski(X31,X31),X30)
        | ~ v1_relat_1(X30) )
      & ( r2_hidden(esk7_1(X30),k3_relat_1(X30))
        | v1_relat_2(X30)
        | ~ v1_relat_1(X30) )
      & ( ~ r2_hidden(k4_tarski(esk7_1(X30),esk7_1(X30)),X30)
        | v1_relat_2(X30)
        | ~ v1_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_wellord1])])])])])).

cnf(c_0_50,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk1_0,esk2_0),esk3_0)
    | ~ r1_tarski(k1_wellord1(esk3_0,esk1_0),k1_wellord1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_51,negated_conjecture,
    ( esk2_0 = esk1_0
    | r1_tarski(k1_wellord1(esk3_0,esk1_0),k1_wellord1(esk3_0,esk2_0))
    | r2_hidden(esk2_0,k1_wellord1(esk3_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( esk2_0 = esk1_0
    | ~ v4_relat_2(esk3_0)
    | ~ r2_hidden(k4_tarski(esk2_0,esk1_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_35]),c_0_14])])).

cnf(c_0_53,plain,
    ( v4_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_54,plain,
    ( r2_hidden(k4_tarski(X2,X2),X1)
    | ~ v1_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( esk2_0 = esk1_0
    | r2_hidden(esk2_0,k1_wellord1(esk3_0,esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_35])).

cnf(c_0_56,negated_conjecture,
    ( esk2_0 = esk1_0
    | ~ r2_hidden(k4_tarski(esk2_0,esk1_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_13]),c_0_14])])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_0,esk1_0),esk3_0)
    | ~ v1_relat_2(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_22]),c_0_14])])).

cnf(c_0_58,plain,
    ( v1_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_59,negated_conjecture,
    ( esk2_0 = esk1_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_55]),c_0_14])]),c_0_56])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_37])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_0,esk1_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_13]),c_0_14])])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_59]),c_0_60]),c_0_59]),c_0_61])]),
    [proof]).
%------------------------------------------------------------------------------
