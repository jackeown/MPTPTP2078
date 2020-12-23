%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t181_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:55 EDT 2019

% Result     : Theorem 266.00s
% Output     : CNFRefutation 266.00s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 798 expanded)
%              Number of clauses        :   46 ( 345 expanded)
%              Number of leaves         :    4 ( 181 expanded)
%              Depth                    :   22
%              Number of atoms          :  241 (4176 expanded)
%              Number of equality atoms :   53 ( 921 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t181_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k10_relat_1(k5_relat_1(X2,X3),X1) = k10_relat_1(X2,k10_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t181_relat_1.p',t181_relat_1)).

fof(d14_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X4,X5),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t181_relat_1.p',d14_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/relat_1__t181_relat_1.p',d8_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t181_relat_1.p',dt_k5_relat_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => k10_relat_1(k5_relat_1(X2,X3),X1) = k10_relat_1(X2,k10_relat_1(X3,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t181_relat_1])).

fof(c_0_5,plain,(
    ! [X12,X13,X14,X15,X17,X18,X19,X20,X22] :
      ( ( r2_hidden(k4_tarski(X15,esk4_4(X12,X13,X14,X15)),X12)
        | ~ r2_hidden(X15,X14)
        | X14 != k10_relat_1(X12,X13)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(esk4_4(X12,X13,X14,X15),X13)
        | ~ r2_hidden(X15,X14)
        | X14 != k10_relat_1(X12,X13)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(k4_tarski(X17,X18),X12)
        | ~ r2_hidden(X18,X13)
        | r2_hidden(X17,X14)
        | X14 != k10_relat_1(X12,X13)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(esk5_3(X12,X19,X20),X20)
        | ~ r2_hidden(k4_tarski(esk5_3(X12,X19,X20),X22),X12)
        | ~ r2_hidden(X22,X19)
        | X20 = k10_relat_1(X12,X19)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(k4_tarski(esk5_3(X12,X19,X20),esk6_3(X12,X19,X20)),X12)
        | r2_hidden(esk5_3(X12,X19,X20),X20)
        | X20 = k10_relat_1(X12,X19)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(esk6_3(X12,X19,X20),X19)
        | r2_hidden(esk5_3(X12,X19,X20),X20)
        | X20 = k10_relat_1(X12,X19)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & k10_relat_1(k5_relat_1(esk2_0,esk3_0),esk1_0) != k10_relat_1(esk2_0,k10_relat_1(esk3_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_7,plain,
    ( r2_hidden(k4_tarski(X1,esk4_4(X2,X3,X4,X1)),X2)
    | ~ r2_hidden(X1,X4)
    | X4 != k10_relat_1(X2,X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | r2_hidden(esk5_3(X1,X2,X3),X3)
    | X3 = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X24,X25,X26,X27,X28,X30,X31,X32,X35] :
      ( ( r2_hidden(k4_tarski(X27,esk7_5(X24,X25,X26,X27,X28)),X24)
        | ~ r2_hidden(k4_tarski(X27,X28),X26)
        | X26 != k5_relat_1(X24,X25)
        | ~ v1_relat_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(k4_tarski(esk7_5(X24,X25,X26,X27,X28),X28),X25)
        | ~ r2_hidden(k4_tarski(X27,X28),X26)
        | X26 != k5_relat_1(X24,X25)
        | ~ v1_relat_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24) )
      & ( ~ r2_hidden(k4_tarski(X30,X32),X24)
        | ~ r2_hidden(k4_tarski(X32,X31),X25)
        | r2_hidden(k4_tarski(X30,X31),X26)
        | X26 != k5_relat_1(X24,X25)
        | ~ v1_relat_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24) )
      & ( ~ r2_hidden(k4_tarski(esk8_3(X24,X25,X26),esk9_3(X24,X25,X26)),X26)
        | ~ r2_hidden(k4_tarski(esk8_3(X24,X25,X26),X35),X24)
        | ~ r2_hidden(k4_tarski(X35,esk9_3(X24,X25,X26)),X25)
        | X26 = k5_relat_1(X24,X25)
        | ~ v1_relat_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(k4_tarski(esk8_3(X24,X25,X26),esk10_3(X24,X25,X26)),X24)
        | r2_hidden(k4_tarski(esk8_3(X24,X25,X26),esk9_3(X24,X25,X26)),X26)
        | X26 = k5_relat_1(X24,X25)
        | ~ v1_relat_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(k4_tarski(esk10_3(X24,X25,X26),esk9_3(X24,X25,X26)),X25)
        | r2_hidden(k4_tarski(esk8_3(X24,X25,X26),esk9_3(X24,X25,X26)),X26)
        | X26 = k5_relat_1(X24,X25)
        | ~ v1_relat_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

fof(c_0_11,plain,(
    ! [X37,X38] :
      ( ~ v1_relat_1(X37)
      | ~ v1_relat_1(X38)
      | v1_relat_1(k5_relat_1(X37,X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X1,esk4_4(X2,X3,k10_relat_1(X2,X3),X1)),X2)
    | ~ r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( X1 = k10_relat_1(esk2_0,X2)
    | r2_hidden(esk5_3(esk2_0,X2,X1),X1)
    | r2_hidden(esk6_3(esk2_0,X2,X1),X2) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,X4),X6)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X2,X4),X5)
    | X6 != k5_relat_1(X3,X5)
    | ~ v1_relat_1(X6)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( X1 = k10_relat_1(esk2_0,k10_relat_1(X2,X3))
    | r2_hidden(k4_tarski(esk6_3(esk2_0,k10_relat_1(X2,X3),X1),esk4_4(X2,X3,k10_relat_1(X2,X3),esk6_3(esk2_0,k10_relat_1(X2,X3),X1))),X2)
    | r2_hidden(esk5_3(esk2_0,k10_relat_1(X2,X3),X1),X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,X4))
    | ~ r2_hidden(k4_tarski(X5,X2),X4)
    | ~ r2_hidden(k4_tarski(X1,X5),X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( X1 = k10_relat_1(esk2_0,k10_relat_1(esk3_0,X2))
    | r2_hidden(k4_tarski(esk6_3(esk2_0,k10_relat_1(esk3_0,X2),X1),esk4_4(esk3_0,X2,k10_relat_1(esk3_0,X2),esk6_3(esk2_0,k10_relat_1(esk3_0,X2),X1))),esk3_0)
    | r2_hidden(esk5_3(esk2_0,k10_relat_1(esk3_0,X2),X1),X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,X2,X3),esk6_3(X1,X2,X3)),X1)
    | r2_hidden(esk5_3(X1,X2,X3),X3)
    | X3 = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_22,negated_conjecture,
    ( X1 = k10_relat_1(esk2_0,k10_relat_1(esk3_0,X2))
    | r2_hidden(k4_tarski(X3,esk4_4(esk3_0,X2,k10_relat_1(esk3_0,X2),esk6_3(esk2_0,k10_relat_1(esk3_0,X2),X1))),k5_relat_1(X4,esk3_0))
    | r2_hidden(esk5_3(esk2_0,k10_relat_1(esk3_0,X2),X1),X1)
    | ~ r2_hidden(k4_tarski(X3,esk6_3(esk2_0,k10_relat_1(esk3_0,X2),X1)),X4)
    | ~ v1_relat_1(X4) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_17])])).

cnf(c_0_23,negated_conjecture,
    ( X1 = k10_relat_1(esk2_0,X2)
    | r2_hidden(k4_tarski(esk5_3(esk2_0,X2,X1),esk6_3(esk2_0,X2,X1)),esk2_0)
    | r2_hidden(esk5_3(esk2_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_9])).

cnf(c_0_24,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( X1 = k10_relat_1(esk2_0,k10_relat_1(esk3_0,X2))
    | r2_hidden(k4_tarski(esk5_3(esk2_0,k10_relat_1(esk3_0,X2),X1),esk4_4(esk3_0,X2,k10_relat_1(esk3_0,X2),esk6_3(esk2_0,k10_relat_1(esk3_0,X2),X1))),k5_relat_1(esk2_0,esk3_0))
    | r2_hidden(esk5_3(esk2_0,k10_relat_1(esk3_0,X2),X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_9])])).

cnf(c_0_27,plain,
    ( r2_hidden(esk4_4(X1,X2,k10_relat_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k10_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( X1 = k10_relat_1(esk2_0,k10_relat_1(esk3_0,X2))
    | r2_hidden(esk5_3(esk2_0,k10_relat_1(esk3_0,X2),X1),k10_relat_1(k5_relat_1(esk2_0,esk3_0),X3))
    | r2_hidden(esk5_3(esk2_0,k10_relat_1(esk3_0,X2),X1),X1)
    | ~ r2_hidden(esk4_4(esk3_0,X2,k10_relat_1(esk3_0,X2),esk6_3(esk2_0,k10_relat_1(esk3_0,X2),X1)),X3)
    | ~ v1_relat_1(k5_relat_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( X1 = k10_relat_1(esk2_0,k10_relat_1(X2,X3))
    | r2_hidden(esk4_4(X2,X3,k10_relat_1(X2,X3),esk6_3(esk2_0,k10_relat_1(X2,X3),X1)),X3)
    | r2_hidden(esk5_3(esk2_0,k10_relat_1(X2,X3),X1),X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_13])).

cnf(c_0_30,negated_conjecture,
    ( X1 = k10_relat_1(esk2_0,k10_relat_1(esk3_0,X2))
    | r2_hidden(esk5_3(esk2_0,k10_relat_1(esk3_0,X2),X1),k10_relat_1(k5_relat_1(esk2_0,esk3_0),X3))
    | r2_hidden(esk5_3(esk2_0,k10_relat_1(esk3_0,X2),X1),X1)
    | ~ r2_hidden(esk4_4(esk3_0,X2,k10_relat_1(esk3_0,X2),esk6_3(esk2_0,k10_relat_1(esk3_0,X2),X1)),X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_15]),c_0_17]),c_0_9])])).

cnf(c_0_31,negated_conjecture,
    ( X1 = k10_relat_1(esk2_0,k10_relat_1(esk3_0,X2))
    | r2_hidden(esk4_4(esk3_0,X2,k10_relat_1(esk3_0,X2),esk6_3(esk2_0,k10_relat_1(esk3_0,X2),X1)),X2)
    | r2_hidden(esk5_3(esk2_0,k10_relat_1(esk3_0,X2),X1),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_17])).

cnf(c_0_32,negated_conjecture,
    ( X1 = k10_relat_1(esk2_0,k10_relat_1(esk3_0,X2))
    | r2_hidden(esk5_3(esk2_0,k10_relat_1(esk3_0,X2),X1),k10_relat_1(k5_relat_1(esk2_0,esk3_0),X2))
    | r2_hidden(esk5_3(esk2_0,k10_relat_1(esk3_0,X2),X1),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_33,negated_conjecture,
    ( k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1) = k10_relat_1(esk2_0,k10_relat_1(esk3_0,X1))
    | r2_hidden(esk5_3(esk2_0,k10_relat_1(esk3_0,X1),k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1)),k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1)) ),
    inference(ef,[status(thm)],[c_0_32])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(X1,esk7_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,negated_conjecture,
    ( k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1) = k10_relat_1(esk2_0,k10_relat_1(esk3_0,X1))
    | r2_hidden(k4_tarski(esk5_3(esk2_0,k10_relat_1(esk3_0,X1),k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1)),esk4_4(k5_relat_1(esk2_0,esk3_0),X1,k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1),esk5_3(esk2_0,k10_relat_1(esk3_0,X1),k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1)))),k5_relat_1(esk2_0,esk3_0))
    | ~ v1_relat_1(k5_relat_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_33])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(esk7_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(X1,esk7_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)
    | ~ r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_34]),c_0_15])).

cnf(c_0_38,negated_conjecture,
    ( k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1) = k10_relat_1(esk2_0,k10_relat_1(esk3_0,X1))
    | r2_hidden(k4_tarski(esk5_3(esk2_0,k10_relat_1(esk3_0,X1),k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1)),esk4_4(k5_relat_1(esk2_0,esk3_0),X1,k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1),esk5_3(esk2_0,k10_relat_1(esk3_0,X1),k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1)))),k5_relat_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_15]),c_0_17]),c_0_9])])).

cnf(c_0_39,plain,
    ( r2_hidden(k4_tarski(esk7_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_36]),c_0_15])).

cnf(c_0_40,negated_conjecture,
    ( k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1) = k10_relat_1(esk2_0,k10_relat_1(esk3_0,X1))
    | r2_hidden(k4_tarski(esk5_3(esk2_0,k10_relat_1(esk3_0,X1),k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1)),esk7_5(esk2_0,esk3_0,k5_relat_1(esk2_0,esk3_0),esk5_3(esk2_0,k10_relat_1(esk3_0,X1),k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1)),esk4_4(k5_relat_1(esk2_0,esk3_0),X1,k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1),esk5_3(esk2_0,k10_relat_1(esk3_0,X1),k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1))))),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_17]),c_0_9])])).

cnf(c_0_41,negated_conjecture,
    ( k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1) = k10_relat_1(esk2_0,k10_relat_1(esk3_0,X1))
    | r2_hidden(k4_tarski(esk7_5(esk2_0,esk3_0,k5_relat_1(esk2_0,esk3_0),esk5_3(esk2_0,k10_relat_1(esk3_0,X1),k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1)),esk4_4(k5_relat_1(esk2_0,esk3_0),X1,k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1),esk5_3(esk2_0,k10_relat_1(esk3_0,X1),k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1)))),esk4_4(k5_relat_1(esk2_0,esk3_0),X1,k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1),esk5_3(esk2_0,k10_relat_1(esk3_0,X1),k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1)))),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_38]),c_0_17]),c_0_9])])).

cnf(c_0_42,negated_conjecture,
    ( k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1) = k10_relat_1(esk2_0,k10_relat_1(esk3_0,X1))
    | r2_hidden(esk5_3(esk2_0,k10_relat_1(esk3_0,X1),k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1)),k10_relat_1(esk2_0,X2))
    | ~ r2_hidden(esk7_5(esk2_0,esk3_0,k5_relat_1(esk2_0,esk3_0),esk5_3(esk2_0,k10_relat_1(esk3_0,X1),k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1)),esk4_4(k5_relat_1(esk2_0,esk3_0),X1,k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1),esk5_3(esk2_0,k10_relat_1(esk3_0,X1),k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1)))),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_40]),c_0_9])])).

cnf(c_0_43,negated_conjecture,
    ( k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1) = k10_relat_1(esk2_0,k10_relat_1(esk3_0,X1))
    | r2_hidden(esk7_5(esk2_0,esk3_0,k5_relat_1(esk2_0,esk3_0),esk5_3(esk2_0,k10_relat_1(esk3_0,X1),k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1)),esk4_4(k5_relat_1(esk2_0,esk3_0),X1,k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1),esk5_3(esk2_0,k10_relat_1(esk3_0,X1),k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1)))),k10_relat_1(esk3_0,X2))
    | ~ r2_hidden(esk4_4(k5_relat_1(esk2_0,esk3_0),X1,k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1),esk5_3(esk2_0,k10_relat_1(esk3_0,X1),k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1))),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_41]),c_0_17])])).

cnf(c_0_44,negated_conjecture,
    ( k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1) = k10_relat_1(esk2_0,k10_relat_1(esk3_0,X1))
    | r2_hidden(esk4_4(k5_relat_1(esk2_0,esk3_0),X1,k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1),esk5_3(esk2_0,k10_relat_1(esk3_0,X1),k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1))),X1)
    | ~ v1_relat_1(k5_relat_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1) = k10_relat_1(esk2_0,k10_relat_1(esk3_0,X1))
    | r2_hidden(esk5_3(esk2_0,k10_relat_1(esk3_0,X1),k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1)),k10_relat_1(esk2_0,k10_relat_1(esk3_0,X2)))
    | ~ r2_hidden(esk4_4(k5_relat_1(esk2_0,esk3_0),X1,k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1),esk5_3(esk2_0,k10_relat_1(esk3_0,X1),k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1))),X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1) = k10_relat_1(esk2_0,k10_relat_1(esk3_0,X1))
    | r2_hidden(esk4_4(k5_relat_1(esk2_0,esk3_0),X1,k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1),esk5_3(esk2_0,k10_relat_1(esk3_0,X1),k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_15]),c_0_17]),c_0_9])])).

cnf(c_0_47,plain,
    ( X3 = k10_relat_1(X1,X2)
    | ~ r2_hidden(esk5_3(X1,X2,X3),X3)
    | ~ r2_hidden(k4_tarski(esk5_3(X1,X2,X3),X4),X1)
    | ~ r2_hidden(X4,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_48,negated_conjecture,
    ( k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1) = k10_relat_1(esk2_0,k10_relat_1(esk3_0,X1))
    | r2_hidden(esk5_3(esk2_0,k10_relat_1(esk3_0,X1),k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1)),k10_relat_1(esk2_0,k10_relat_1(esk3_0,X1))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1) = k10_relat_1(esk2_0,k10_relat_1(esk3_0,X1))
    | ~ r2_hidden(k4_tarski(esk5_3(esk2_0,k10_relat_1(esk3_0,X1),k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1)),X2),esk2_0)
    | ~ r2_hidden(X2,k10_relat_1(esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_33]),c_0_9])])).

cnf(c_0_50,negated_conjecture,
    ( k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1) = k10_relat_1(esk2_0,k10_relat_1(esk3_0,X1))
    | r2_hidden(esk4_4(esk2_0,k10_relat_1(esk3_0,X1),k10_relat_1(esk2_0,k10_relat_1(esk3_0,X1)),esk5_3(esk2_0,k10_relat_1(esk3_0,X1),k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1))),k10_relat_1(esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_48]),c_0_9])])).

cnf(c_0_51,negated_conjecture,
    ( k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1) = k10_relat_1(esk2_0,k10_relat_1(esk3_0,X1))
    | ~ r2_hidden(k4_tarski(esk5_3(esk2_0,k10_relat_1(esk3_0,X1),k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1)),esk4_4(esk2_0,k10_relat_1(esk3_0,X1),k10_relat_1(esk2_0,k10_relat_1(esk3_0,X1)),esk5_3(esk2_0,k10_relat_1(esk3_0,X1),k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1)))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_52,negated_conjecture,
    ( k10_relat_1(k5_relat_1(esk2_0,esk3_0),esk1_0) != k10_relat_1(esk2_0,k10_relat_1(esk3_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_53,negated_conjecture,
    ( k10_relat_1(k5_relat_1(esk2_0,esk3_0),X1) = k10_relat_1(esk2_0,k10_relat_1(esk3_0,X1)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_48]),c_0_9])]),c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53])]),
    [proof]).
%------------------------------------------------------------------------------
