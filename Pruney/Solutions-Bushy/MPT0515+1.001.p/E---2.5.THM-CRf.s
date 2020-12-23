%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0515+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:44 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 123 expanded)
%              Number of clauses        :   29 (  57 expanded)
%              Number of leaves         :    4 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  175 ( 673 expanded)
%              Number of equality atoms :   34 ( 115 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d12_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( X3 = k8_relat_1(X1,X2)
          <=> ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X3)
              <=> ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X4,X5),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(t115_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k2_relat_1(k8_relat_1(X2,X3)))
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X1,k2_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_relat_1)).

fof(c_0_4,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X10,X6)
        | ~ r2_hidden(k4_tarski(X9,X10),X8)
        | X8 != k8_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(k4_tarski(X9,X10),X7)
        | ~ r2_hidden(k4_tarski(X9,X10),X8)
        | X8 != k8_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(X12,X6)
        | ~ r2_hidden(k4_tarski(X11,X12),X7)
        | r2_hidden(k4_tarski(X11,X12),X8)
        | X8 != k8_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | ~ r2_hidden(esk2_3(X6,X7,X8),X6)
        | ~ r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X7)
        | X8 = k8_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(esk2_3(X6,X7,X8),X6)
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | X8 = k8_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X7)
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | X8 = k8_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_1])])])])])])).

fof(c_0_5,plain,(
    ! [X15,X16,X17,X19,X20,X21,X22,X24] :
      ( ( ~ r2_hidden(X17,X16)
        | r2_hidden(k4_tarski(esk3_3(X15,X16,X17),X17),X15)
        | X16 != k2_relat_1(X15) )
      & ( ~ r2_hidden(k4_tarski(X20,X19),X15)
        | r2_hidden(X19,X16)
        | X16 != k2_relat_1(X15) )
      & ( ~ r2_hidden(esk4_2(X21,X22),X22)
        | ~ r2_hidden(k4_tarski(X24,esk4_2(X21,X22)),X21)
        | X22 = k2_relat_1(X21) )
      & ( r2_hidden(esk4_2(X21,X22),X22)
        | r2_hidden(k4_tarski(esk5_2(X21,X22),esk4_2(X21,X22)),X21)
        | X22 = k2_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_6,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X4)
    | X4 != k8_relat_1(X5,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( r2_hidden(k4_tarski(esk3_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X27)
      | v1_relat_1(k8_relat_1(X26,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

cnf(c_0_9,plain,
    ( r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X3),X4)
    | X1 != k8_relat_1(X5,X4)
    | X2 != k2_relat_1(X1)
    | ~ r2_hidden(X3,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X4) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),X4)
    | X4 != k8_relat_1(X2,X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X3,X1),X5)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),X4)
    | X5 != k8_relat_1(X2,X4)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(esk3_3(k8_relat_1(X1,X2),X3,X4),X4),X2)
    | X3 != k2_relat_1(k8_relat_1(X1,X2))
    | ~ r2_hidden(X4,X3)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_9]),c_0_10])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r2_hidden(X1,k2_relat_1(k8_relat_1(X2,X3)))
        <=> ( r2_hidden(X1,X2)
            & r2_hidden(X1,k2_relat_1(X3)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t115_relat_1])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | X3 != k8_relat_1(X2,X4)
    | X5 != k2_relat_1(X3)
    | ~ r2_hidden(X1,X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_11,c_0_7])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X3),X4)
    | X4 != k8_relat_1(X5,X1)
    | X2 != k2_relat_1(X1)
    | ~ r2_hidden(X3,X5)
    | ~ r2_hidden(X3,X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_7])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | X3 != k2_relat_1(k8_relat_1(X4,X5))
    | X2 != k2_relat_1(X5)
    | ~ r2_hidden(X1,X3)
    | ~ v1_relat_1(X5) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_19,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & ( ~ r2_hidden(esk6_0,k2_relat_1(k8_relat_1(esk7_0,esk8_0)))
      | ~ r2_hidden(esk6_0,esk7_0)
      | ~ r2_hidden(esk6_0,k2_relat_1(esk8_0)) )
    & ( r2_hidden(esk6_0,esk7_0)
      | r2_hidden(esk6_0,k2_relat_1(k8_relat_1(esk7_0,esk8_0))) )
    & ( r2_hidden(esk6_0,k2_relat_1(esk8_0))
      | r2_hidden(esk6_0,k2_relat_1(k8_relat_1(esk7_0,esk8_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | X3 != k2_relat_1(k8_relat_1(X2,X4))
    | ~ r2_hidden(X1,X3)
    | ~ v1_relat_1(X4) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_16]),c_0_10])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X3),k8_relat_1(X4,X1))
    | X2 != k2_relat_1(X1)
    | ~ r2_hidden(X3,X4)
    | ~ r2_hidden(X3,X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_17]),c_0_10])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3)
    | ~ r2_hidden(X1,k2_relat_1(k8_relat_1(X4,X3)))
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk6_0,k2_relat_1(esk8_0))
    | r2_hidden(esk6_0,k2_relat_1(k8_relat_1(esk7_0,esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_relat_1(k8_relat_1(X2,X3)))
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk6_0,esk7_0)
    | r2_hidden(esk6_0,k2_relat_1(k8_relat_1(esk7_0,esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_relat_1(k8_relat_1(X3,X4))
    | X5 != k2_relat_1(X4)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X5)
    | ~ v1_relat_1(X4) ),
    inference(spm,[status(thm)],[c_0_13,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk6_0,k2_relat_1(esk8_0))
    | r2_hidden(esk6_0,X1)
    | X1 != k2_relat_1(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_29,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k2_relat_1(k8_relat_1(esk7_0,esk8_0)))
    | ~ r2_hidden(esk6_0,esk7_0)
    | ~ r2_hidden(esk6_0,k2_relat_1(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_24])])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k2_relat_1(k8_relat_1(X2,X3)))
    | X4 != k2_relat_1(X3)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk6_0,k2_relat_1(esk8_0)) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k2_relat_1(k8_relat_1(esk7_0,esk8_0)))
    | ~ r2_hidden(esk6_0,k2_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk6_0,k2_relat_1(k8_relat_1(X1,X2)))
    | k2_relat_1(esk8_0) != k2_relat_1(X2)
    | ~ r2_hidden(esk6_0,X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k2_relat_1(k8_relat_1(esk7_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_32])])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk6_0,k2_relat_1(k8_relat_1(X1,esk8_0)))
    | ~ r2_hidden(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_34]),c_0_24])])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_30])]),
    [proof]).

%------------------------------------------------------------------------------
