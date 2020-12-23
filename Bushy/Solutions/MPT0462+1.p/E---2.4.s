%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t50_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:03 EDT 2019

% Result     : Theorem 0.49s
% Output     : CNFRefutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 135 expanded)
%              Number of clauses        :   29 (  50 expanded)
%              Number of leaves         :    4 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :  155 ( 746 expanded)
%              Number of equality atoms :   10 (  24 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   38 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ! [X4] :
                  ( v1_relat_1(X4)
                 => ( ( r1_tarski(X1,X2)
                      & r1_tarski(X3,X4) )
                   => r1_tarski(k5_relat_1(X1,X3),k5_relat_1(X2,X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t50_relat_1.p',t50_relat_1)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t50_relat_1.p',d3_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/relat_1__t50_relat_1.p',d8_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t50_relat_1.p',dt_k5_relat_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => ! [X4] :
                    ( v1_relat_1(X4)
                   => ( ( r1_tarski(X1,X2)
                        & r1_tarski(X3,X4) )
                     => r1_tarski(k5_relat_1(X1,X3),k5_relat_1(X2,X4)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_relat_1])).

fof(c_0_5,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & v1_relat_1(esk4_0)
    & r1_tarski(esk1_0,esk2_0)
    & r1_tarski(esk3_0,esk4_0)
    & ~ r1_tarski(k5_relat_1(esk1_0,esk3_0),k5_relat_1(esk2_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_6,plain,(
    ! [X13,X14,X15,X16,X17] :
      ( ( ~ r1_tarski(X13,X14)
        | ~ r2_hidden(k4_tarski(X15,X16),X13)
        | r2_hidden(k4_tarski(X15,X16),X14)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(esk5_2(X13,X17),esk6_2(X13,X17)),X13)
        | r1_tarski(X13,X17)
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(k4_tarski(esk5_2(X13,X17),esk6_2(X13,X17)),X17)
        | r1_tarski(X13,X17)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

fof(c_0_7,plain,(
    ! [X20,X21,X22,X23,X24,X26,X27,X28,X31] :
      ( ( r2_hidden(k4_tarski(X23,esk7_5(X20,X21,X22,X23,X24)),X20)
        | ~ r2_hidden(k4_tarski(X23,X24),X22)
        | X22 != k5_relat_1(X20,X21)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(k4_tarski(esk7_5(X20,X21,X22,X23,X24),X24),X21)
        | ~ r2_hidden(k4_tarski(X23,X24),X22)
        | X22 != k5_relat_1(X20,X21)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(X26,X28),X20)
        | ~ r2_hidden(k4_tarski(X28,X27),X21)
        | r2_hidden(k4_tarski(X26,X27),X22)
        | X22 != k5_relat_1(X20,X21)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(esk8_3(X20,X21,X22),esk9_3(X20,X21,X22)),X22)
        | ~ r2_hidden(k4_tarski(esk8_3(X20,X21,X22),X31),X20)
        | ~ r2_hidden(k4_tarski(X31,esk9_3(X20,X21,X22)),X21)
        | X22 = k5_relat_1(X20,X21)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(k4_tarski(esk8_3(X20,X21,X22),esk10_3(X20,X21,X22)),X20)
        | r2_hidden(k4_tarski(esk8_3(X20,X21,X22),esk9_3(X20,X21,X22)),X22)
        | X22 = k5_relat_1(X20,X21)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(k4_tarski(esk10_3(X20,X21,X22),esk9_3(X20,X21,X22)),X21)
        | r2_hidden(k4_tarski(esk8_3(X20,X21,X22),esk9_3(X20,X21,X22)),X22)
        | X22 = k5_relat_1(X20,X21)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

fof(c_0_8,plain,(
    ! [X33,X34] :
      ( ~ v1_relat_1(X33)
      | ~ v1_relat_1(X34)
      | v1_relat_1(k5_relat_1(X33,X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_9,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk1_0,esk3_0),k5_relat_1(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(esk5_2(X1,X2),esk6_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(k4_tarski(esk7_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_2(k5_relat_1(esk1_0,esk3_0),k5_relat_1(esk2_0,esk4_0)),esk6_2(k5_relat_1(esk1_0,esk3_0),k5_relat_1(esk2_0,esk4_0))),k5_relat_1(esk1_0,esk3_0))
    | ~ v1_relat_1(k5_relat_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(X3,X4),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(esk7_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_2(k5_relat_1(esk1_0,esk3_0),k5_relat_1(esk2_0,esk4_0)),esk6_2(k5_relat_1(esk1_0,esk3_0),k5_relat_1(esk2_0,esk4_0))),k5_relat_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_12]),c_0_14]),c_0_15])])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(X1,esk7_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X1,X4),X6)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X2,X4),X5)
    | X6 != k5_relat_1(X3,X5)
    | ~ v1_relat_1(X6)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk4_0)
    | ~ r2_hidden(k4_tarski(X1,X2),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_14])])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_5(esk1_0,esk3_0,k5_relat_1(esk1_0,esk3_0),esk5_2(k5_relat_1(esk1_0,esk3_0),k5_relat_1(esk2_0,esk4_0)),esk6_2(k5_relat_1(esk1_0,esk3_0),k5_relat_1(esk2_0,esk4_0))),esk6_2(k5_relat_1(esk1_0,esk3_0),k5_relat_1(esk2_0,esk4_0))),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_14]),c_0_15])])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(X1,esk7_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)
    | ~ r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_20]),c_0_12])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,X4))
    | ~ r2_hidden(k4_tarski(X5,X2),X4)
    | ~ r2_hidden(k4_tarski(X1,X5),X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_21]),c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_5(esk1_0,esk3_0,k5_relat_1(esk1_0,esk3_0),esk5_2(k5_relat_1(esk1_0,esk3_0),k5_relat_1(esk2_0,esk4_0)),esk6_2(k5_relat_1(esk1_0,esk3_0),k5_relat_1(esk2_0,esk4_0))),esk6_2(k5_relat_1(esk1_0,esk3_0),k5_relat_1(esk2_0,esk4_0))),esk4_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk2_0)
    | ~ r2_hidden(k4_tarski(X1,X2),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_24]),c_0_15])])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_2(k5_relat_1(esk1_0,esk3_0),k5_relat_1(esk2_0,esk4_0)),esk7_5(esk1_0,esk3_0,k5_relat_1(esk1_0,esk3_0),esk5_2(k5_relat_1(esk1_0,esk3_0),k5_relat_1(esk2_0,esk4_0)),esk6_2(k5_relat_1(esk1_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_19]),c_0_14]),c_0_15])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk6_2(k5_relat_1(esk1_0,esk3_0),k5_relat_1(esk2_0,esk4_0))),k5_relat_1(X2,esk4_0))
    | ~ r2_hidden(k4_tarski(X1,esk7_5(esk1_0,esk3_0,k5_relat_1(esk1_0,esk3_0),esk5_2(k5_relat_1(esk1_0,esk3_0),k5_relat_1(esk2_0,esk4_0)),esk6_2(k5_relat_1(esk1_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))),X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_2(k5_relat_1(esk1_0,esk3_0),k5_relat_1(esk2_0,esk4_0)),esk7_5(esk1_0,esk3_0,k5_relat_1(esk1_0,esk3_0),esk5_2(k5_relat_1(esk1_0,esk3_0),k5_relat_1(esk2_0,esk4_0)),esk6_2(k5_relat_1(esk1_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk5_2(X1,X2),esk6_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_2(k5_relat_1(esk1_0,esk3_0),k5_relat_1(esk2_0,esk4_0)),esk6_2(k5_relat_1(esk1_0,esk3_0),k5_relat_1(esk2_0,esk4_0))),k5_relat_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_36,negated_conjecture,
    ( ~ v1_relat_1(k5_relat_1(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_9])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_12]),c_0_14]),c_0_15])]),
    [proof]).
%------------------------------------------------------------------------------
