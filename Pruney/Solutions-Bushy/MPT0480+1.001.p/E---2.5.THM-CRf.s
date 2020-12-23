%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0480+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:42 EST 2020

% Result     : Theorem 0.23s
% Output     : CNFRefutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 199 expanded)
%              Number of clauses        :   32 (  85 expanded)
%              Number of leaves         :    5 (  50 expanded)
%              Depth                    :   17
%              Number of atoms          :  214 (1172 expanded)
%              Number of equality atoms :   43 ( 205 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t75_relat_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X4,k6_relat_1(X3)))
      <=> ( r2_hidden(X2,X3)
          & r2_hidden(k4_tarski(X1,X2),X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(c_0_5,plain,(
    ! [X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X9,X7)
        | ~ r2_hidden(k4_tarski(X9,X10),X8)
        | X8 != k6_relat_1(X7)
        | ~ v1_relat_1(X8) )
      & ( X9 = X10
        | ~ r2_hidden(k4_tarski(X9,X10),X8)
        | X8 != k6_relat_1(X7)
        | ~ v1_relat_1(X8) )
      & ( ~ r2_hidden(X11,X7)
        | X11 != X12
        | r2_hidden(k4_tarski(X11,X12),X8)
        | X8 != k6_relat_1(X7)
        | ~ v1_relat_1(X8) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X8)
        | ~ r2_hidden(esk1_2(X7,X8),X7)
        | esk1_2(X7,X8) != esk2_2(X7,X8)
        | X8 = k6_relat_1(X7)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X8)
        | X8 = k6_relat_1(X7)
        | ~ v1_relat_1(X8) )
      & ( esk1_2(X7,X8) = esk2_2(X7,X8)
        | r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X8)
        | X8 = k6_relat_1(X7)
        | ~ v1_relat_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_relat_1])])])])])])).

fof(c_0_6,plain,(
    ! [X15,X16,X17,X18,X19,X21,X22,X23,X26] :
      ( ( r2_hidden(k4_tarski(X18,esk3_5(X15,X16,X17,X18,X19)),X15)
        | ~ r2_hidden(k4_tarski(X18,X19),X17)
        | X17 != k5_relat_1(X15,X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(k4_tarski(esk3_5(X15,X16,X17,X18,X19),X19),X16)
        | ~ r2_hidden(k4_tarski(X18,X19),X17)
        | X17 != k5_relat_1(X15,X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) )
      & ( ~ r2_hidden(k4_tarski(X21,X23),X15)
        | ~ r2_hidden(k4_tarski(X23,X22),X16)
        | r2_hidden(k4_tarski(X21,X22),X17)
        | X17 != k5_relat_1(X15,X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) )
      & ( ~ r2_hidden(k4_tarski(esk4_3(X15,X16,X17),esk5_3(X15,X16,X17)),X17)
        | ~ r2_hidden(k4_tarski(esk4_3(X15,X16,X17),X26),X15)
        | ~ r2_hidden(k4_tarski(X26,esk5_3(X15,X16,X17)),X16)
        | X17 = k5_relat_1(X15,X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(k4_tarski(esk4_3(X15,X16,X17),esk6_3(X15,X16,X17)),X15)
        | r2_hidden(k4_tarski(esk4_3(X15,X16,X17),esk5_3(X15,X16,X17)),X17)
        | X17 = k5_relat_1(X15,X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(k4_tarski(esk6_3(X15,X16,X17),esk5_3(X15,X16,X17)),X16)
        | r2_hidden(k4_tarski(esk4_3(X15,X16,X17),esk5_3(X15,X16,X17)),X17)
        | X17 = k5_relat_1(X15,X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

cnf(c_0_7,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X3 != k6_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r2_hidden(k4_tarski(esk3_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X30] : v1_relat_1(k6_relat_1(X30)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_10,plain,
    ( esk3_5(X1,X2,X3,X4,X5) = X5
    | X3 != k5_relat_1(X1,X2)
    | X2 != k6_relat_1(X6)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( v1_relat_1(X4)
       => ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X4,k6_relat_1(X3)))
        <=> ( r2_hidden(X2,X3)
            & r2_hidden(k4_tarski(X1,X2),X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t75_relat_1])).

cnf(c_0_13,plain,
    ( esk3_5(X1,k6_relat_1(X2),X3,X4,X5) = X5
    | X3 != k5_relat_1(X1,k6_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_10]),c_0_11])])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk10_0)
    & ( ~ r2_hidden(k4_tarski(esk7_0,esk8_0),k5_relat_1(esk10_0,k6_relat_1(esk9_0)))
      | ~ r2_hidden(esk8_0,esk9_0)
      | ~ r2_hidden(k4_tarski(esk7_0,esk8_0),esk10_0) )
    & ( r2_hidden(esk8_0,esk9_0)
      | r2_hidden(k4_tarski(esk7_0,esk8_0),k5_relat_1(esk10_0,k6_relat_1(esk9_0))) )
    & ( r2_hidden(k4_tarski(esk7_0,esk8_0),esk10_0)
      | r2_hidden(k4_tarski(esk7_0,esk8_0),k5_relat_1(esk10_0,k6_relat_1(esk9_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(X1,X1),k6_relat_1(X2))
    | X3 != k5_relat_1(X4,k6_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X5,X1),X3)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X4) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_13]),c_0_11])])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk8_0,esk9_0)
    | r2_hidden(k4_tarski(esk7_0,esk8_0),k5_relat_1(esk10_0,k6_relat_1(esk9_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_17,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X28)
      | ~ v1_relat_1(X29)
      | v1_relat_1(k5_relat_1(X28,X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk8_0),k6_relat_1(X1))
    | r2_hidden(esk8_0,esk9_0)
    | k5_relat_1(esk10_0,k6_relat_1(esk9_0)) != k5_relat_1(X2,k6_relat_1(X1))
    | ~ v1_relat_1(k5_relat_1(esk10_0,k6_relat_1(esk9_0)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk8_0),k6_relat_1(X1))
    | r2_hidden(esk8_0,esk9_0)
    | k5_relat_1(esk10_0,k6_relat_1(esk9_0)) != k5_relat_1(X2,k6_relat_1(X1))
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_11]),c_0_20])])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X4 != k6_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk8_0),k6_relat_1(esk9_0))
    | r2_hidden(esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_21]),c_0_20])])).

cnf(c_0_24,plain,
    ( r2_hidden(k4_tarski(X1,X3),X4)
    | ~ r2_hidden(X1,X2)
    | X1 != X3
    | X4 != k6_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk8_0,esk9_0)
    | r2_hidden(esk8_0,X1)
    | k6_relat_1(esk9_0) != k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_11])])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(X1,X1),X2)
    | X2 != k6_relat_1(X3)
    | ~ r2_hidden(X1,X3)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk8_0,esk9_0) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_28,plain,
    ( r2_hidden(k4_tarski(X1,esk3_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk8_0),X1)
    | X1 != k6_relat_1(esk9_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k5_relat_1(X3,k6_relat_1(X5))
    | ~ r2_hidden(k4_tarski(X1,X2),X4)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_13]),c_0_11])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk8_0),esk10_0)
    | r2_hidden(k4_tarski(esk7_0,esk8_0),k5_relat_1(esk10_0,k6_relat_1(esk9_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(X1,X4),X6)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X2,X4),X5)
    | X6 != k5_relat_1(X3,X5)
    | ~ v1_relat_1(X6)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk8_0),k6_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_29]),c_0_11])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk8_0),esk10_0)
    | r2_hidden(k4_tarski(esk7_0,esk8_0),X1)
    | k5_relat_1(esk10_0,k6_relat_1(esk9_0)) != k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(k5_relat_1(esk10_0,k6_relat_1(esk9_0)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk8_0),X2)
    | X2 != k5_relat_1(X3,k6_relat_1(esk9_0))
    | ~ r2_hidden(k4_tarski(X1,esk8_0),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_11])])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk8_0),esk10_0)
    | ~ v1_relat_1(k5_relat_1(esk10_0,k6_relat_1(esk9_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_34]),c_0_20])])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk7_0,esk8_0),k5_relat_1(esk10_0,k6_relat_1(esk9_0)))
    | ~ r2_hidden(esk8_0,esk9_0)
    | ~ r2_hidden(k4_tarski(esk7_0,esk8_0),esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk8_0),X1)
    | X1 != k5_relat_1(esk10_0,k6_relat_1(esk9_0))
    | ~ v1_relat_1(k5_relat_1(esk10_0,k6_relat_1(esk9_0)))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_20])])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk7_0,esk8_0),k5_relat_1(esk10_0,k6_relat_1(esk9_0)))
    | ~ r2_hidden(k4_tarski(esk7_0,esk8_0),esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_27])])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk8_0),k5_relat_1(X1,X2))
    | k5_relat_1(X1,X2) != k5_relat_1(esk10_0,k6_relat_1(esk9_0))
    | ~ v1_relat_1(k5_relat_1(esk10_0,k6_relat_1(esk9_0)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_19])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_relat_1(k5_relat_1(esk10_0,k6_relat_1(esk9_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_11]),c_0_20])]),c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_19]),c_0_11]),c_0_20])]),
    [proof]).

%------------------------------------------------------------------------------
