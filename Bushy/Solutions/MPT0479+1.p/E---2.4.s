%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t74_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:04 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 160 expanded)
%              Number of clauses        :   28 (  68 expanded)
%              Number of leaves         :    5 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :  182 ( 878 expanded)
%              Number of equality atoms :   29 ( 128 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k6_relat_1(X1)
      <=> ! [X3,X4] :
            ( r2_hidden(k4_tarski(X3,X4),X2)
          <=> ( r2_hidden(X3,X1)
              & X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t74_relat_1.p',d10_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t74_relat_1.p',dt_k6_relat_1)).

fof(d8_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( X3 = k5_relat_1(X1,X2)
              <=> ! [X4,X5] :
                    ( r2_hidden(k4_tarski(X4,X5),X3)
                  <=> ? [X6] :
                        ( r2_hidden(k4_tarski(X4,X6),X1)
                        & r2_hidden(k4_tarski(X6,X5),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t74_relat_1.p',d8_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t74_relat_1.p',dt_k5_relat_1)).

fof(t74_relat_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(k6_relat_1(X3),X4))
      <=> ( r2_hidden(X1,X3)
          & r2_hidden(k4_tarski(X1,X2),X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t74_relat_1.p',t74_relat_1)).

fof(c_0_5,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X15,X13)
        | ~ r2_hidden(k4_tarski(X15,X16),X14)
        | X14 != k6_relat_1(X13)
        | ~ v1_relat_1(X14) )
      & ( X15 = X16
        | ~ r2_hidden(k4_tarski(X15,X16),X14)
        | X14 != k6_relat_1(X13)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(X17,X13)
        | X17 != X18
        | r2_hidden(k4_tarski(X17,X18),X14)
        | X14 != k6_relat_1(X13)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(k4_tarski(esk5_2(X13,X14),esk6_2(X13,X14)),X14)
        | ~ r2_hidden(esk5_2(X13,X14),X13)
        | esk5_2(X13,X14) != esk6_2(X13,X14)
        | X14 = k6_relat_1(X13)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(esk5_2(X13,X14),X13)
        | r2_hidden(k4_tarski(esk5_2(X13,X14),esk6_2(X13,X14)),X14)
        | X14 = k6_relat_1(X13)
        | ~ v1_relat_1(X14) )
      & ( esk5_2(X13,X14) = esk6_2(X13,X14)
        | r2_hidden(k4_tarski(esk5_2(X13,X14),esk6_2(X13,X14)),X14)
        | X14 = k6_relat_1(X13)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_relat_1])])])])])])).

fof(c_0_6,plain,(
    ! [X36] : v1_relat_1(k6_relat_1(X36)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_7,plain,(
    ! [X21,X22,X23,X24,X25,X27,X28,X29,X32] :
      ( ( r2_hidden(k4_tarski(X24,esk7_5(X21,X22,X23,X24,X25)),X21)
        | ~ r2_hidden(k4_tarski(X24,X25),X23)
        | X23 != k5_relat_1(X21,X22)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(k4_tarski(esk7_5(X21,X22,X23,X24,X25),X25),X22)
        | ~ r2_hidden(k4_tarski(X24,X25),X23)
        | X23 != k5_relat_1(X21,X22)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21) )
      & ( ~ r2_hidden(k4_tarski(X27,X29),X21)
        | ~ r2_hidden(k4_tarski(X29,X28),X22)
        | r2_hidden(k4_tarski(X27,X28),X23)
        | X23 != k5_relat_1(X21,X22)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21) )
      & ( ~ r2_hidden(k4_tarski(esk8_3(X21,X22,X23),esk9_3(X21,X22,X23)),X23)
        | ~ r2_hidden(k4_tarski(esk8_3(X21,X22,X23),X32),X21)
        | ~ r2_hidden(k4_tarski(X32,esk9_3(X21,X22,X23)),X22)
        | X23 = k5_relat_1(X21,X22)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(k4_tarski(esk8_3(X21,X22,X23),esk10_3(X21,X22,X23)),X21)
        | r2_hidden(k4_tarski(esk8_3(X21,X22,X23),esk9_3(X21,X22,X23)),X23)
        | X23 = k5_relat_1(X21,X22)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(k4_tarski(esk10_3(X21,X22,X23),esk9_3(X21,X22,X23)),X22)
        | r2_hidden(k4_tarski(esk8_3(X21,X22,X23),esk9_3(X21,X22,X23)),X23)
        | X23 = k5_relat_1(X21,X22)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

fof(c_0_8,plain,(
    ! [X34,X35] :
      ( ~ v1_relat_1(X34)
      | ~ v1_relat_1(X35)
      | v1_relat_1(k5_relat_1(X34,X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X4 != k6_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(k4_tarski(X1,esk7_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( v1_relat_1(X4)
       => ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(k6_relat_1(X3),X4))
        <=> ( r2_hidden(X1,X3)
            & r2_hidden(k4_tarski(X1,X2),X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t74_relat_1])).

cnf(c_0_14,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X3 != k6_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_9]),c_0_10])])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(X1,esk7_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)
    | ~ r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_12])).

fof(c_0_17,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & ( ~ r2_hidden(k4_tarski(esk1_0,esk2_0),k5_relat_1(k6_relat_1(esk3_0),esk4_0))
      | ~ r2_hidden(esk1_0,esk3_0)
      | ~ r2_hidden(k4_tarski(esk1_0,esk2_0),esk4_0) )
    & ( r2_hidden(esk1_0,esk3_0)
      | r2_hidden(k4_tarski(esk1_0,esk2_0),k5_relat_1(k6_relat_1(esk3_0),esk4_0)) )
    & ( r2_hidden(k4_tarski(esk1_0,esk2_0),esk4_0)
      | r2_hidden(k4_tarski(esk1_0,esk2_0),k5_relat_1(k6_relat_1(esk3_0),esk4_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(esk7_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X2),k6_relat_1(X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_10])])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k5_relat_1(k6_relat_1(X2),X4))
    | ~ v1_relat_1(X4) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_10])])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0)
    | r2_hidden(k4_tarski(esk1_0,esk2_0),k5_relat_1(k6_relat_1(esk3_0),esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(esk7_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_18]),c_0_12])).

cnf(c_0_24,plain,
    ( esk7_5(k6_relat_1(X1),X2,k5_relat_1(k6_relat_1(X1),X2),X3,X4) = X3
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(k6_relat_1(X1),X2))
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_16]),c_0_10])])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk1_0,esk2_0),k5_relat_1(k6_relat_1(esk3_0),esk4_0))
    | ~ r2_hidden(esk1_0,esk3_0)
    | ~ r2_hidden(k4_tarski(esk1_0,esk2_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),k5_relat_1(k6_relat_1(X4),X3))
    | ~ v1_relat_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_10])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_0,esk2_0),esk4_0)
    | r2_hidden(k4_tarski(esk1_0,esk2_0),k5_relat_1(k6_relat_1(esk3_0),esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(X1,X4),X6)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X2,X4),X5)
    | X6 != k5_relat_1(X3,X5)
    | ~ v1_relat_1(X6)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_30,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk1_0,esk2_0),k5_relat_1(k6_relat_1(esk3_0),esk4_0))
    | ~ r2_hidden(k4_tarski(esk1_0,esk2_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_0,esk2_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_22])])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,X4))
    | ~ r2_hidden(k4_tarski(X5,X2),X4)
    | ~ r2_hidden(k4_tarski(X1,X5),X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_29]),c_0_12])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk1_0,esk2_0),k5_relat_1(k6_relat_1(esk3_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_0),k5_relat_1(X2,esk4_0))
    | ~ r2_hidden(k4_tarski(X1,esk1_0),X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_31]),c_0_22])])).

cnf(c_0_35,plain,
    ( r2_hidden(k4_tarski(X1,X3),X4)
    | ~ r2_hidden(X1,X2)
    | X1 != X3
    | X4 != k6_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_36,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk1_0,esk1_0),k6_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_10])])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(X1,X1),k6_relat_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_35])]),c_0_10])])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
