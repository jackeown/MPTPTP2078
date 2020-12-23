%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:05 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 152 expanded)
%              Number of clauses        :   27 (  64 expanded)
%              Number of leaves         :    5 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :  151 ( 566 expanded)
%              Number of equality atoms :   30 ( 116 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t123_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t75_relat_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X4,k6_relat_1(X3)))
      <=> ( r2_hidden(X2,X3)
          & r2_hidden(k4_tarski(X1,X2),X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_relat_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    inference(assume_negation,[status(cth)],[t123_relat_1])).

fof(c_0_6,plain,(
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

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & k8_relat_1(esk3_0,esk4_0) != k5_relat_1(esk4_0,k6_relat_1(esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_8,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X3)
    | X3 = k8_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | ~ v1_relat_1(X16)
      | v1_relat_1(k5_relat_1(X15,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_11,negated_conjecture,
    ( X1 = k8_relat_1(X2,esk4_0)
    | r2_hidden(k4_tarski(esk1_3(X2,esk4_0,X1),esk2_3(X2,esk4_0,X1)),X1)
    | r2_hidden(esk2_3(X2,esk4_0,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( k5_relat_1(X1,X2) = k8_relat_1(X3,esk4_0)
    | r2_hidden(k4_tarski(esk1_3(X3,esk4_0,k5_relat_1(X1,X2)),esk2_3(X3,esk4_0,k5_relat_1(X1,X2))),k5_relat_1(X1,X2))
    | r2_hidden(esk2_3(X3,esk4_0,k5_relat_1(X1,X2)),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_14,plain,(
    ! [X17] : v1_relat_1(k6_relat_1(X17)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X2)
    | r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X3)
    | X3 = k8_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_16,plain,(
    ! [X18,X19,X20,X21] :
      ( ( r2_hidden(X19,X20)
        | ~ r2_hidden(k4_tarski(X18,X19),k5_relat_1(X21,k6_relat_1(X20)))
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(k4_tarski(X18,X19),X21)
        | ~ r2_hidden(k4_tarski(X18,X19),k5_relat_1(X21,k6_relat_1(X20)))
        | ~ v1_relat_1(X21) )
      & ( ~ r2_hidden(X19,X20)
        | ~ r2_hidden(k4_tarski(X18,X19),X21)
        | r2_hidden(k4_tarski(X18,X19),k5_relat_1(X21,k6_relat_1(X20)))
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t75_relat_1])])])).

cnf(c_0_17,negated_conjecture,
    ( k5_relat_1(esk4_0,X1) = k8_relat_1(X2,esk4_0)
    | r2_hidden(k4_tarski(esk1_3(X2,esk4_0,k5_relat_1(esk4_0,X1)),esk2_3(X2,esk4_0,k5_relat_1(esk4_0,X1))),k5_relat_1(esk4_0,X1))
    | r2_hidden(esk2_3(X2,esk4_0,k5_relat_1(esk4_0,X1)),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_9])).

cnf(c_0_18,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( X1 = k8_relat_1(X2,esk4_0)
    | r2_hidden(k4_tarski(esk1_3(X2,esk4_0,X1),esk2_3(X2,esk4_0,X1)),esk4_0)
    | r2_hidden(k4_tarski(esk1_3(X2,esk4_0,X1),esk2_3(X2,esk4_0,X1)),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_9])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,k6_relat_1(X2)))
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( k5_relat_1(esk4_0,k6_relat_1(X1)) = k8_relat_1(X2,esk4_0)
    | r2_hidden(k4_tarski(esk1_3(X2,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1))),esk2_3(X2,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1)))),k5_relat_1(esk4_0,k6_relat_1(X1)))
    | r2_hidden(esk2_3(X2,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1))),X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( k5_relat_1(X1,X2) = k8_relat_1(X3,esk4_0)
    | r2_hidden(k4_tarski(esk1_3(X3,esk4_0,k5_relat_1(X1,X2)),esk2_3(X3,esk4_0,k5_relat_1(X1,X2))),k5_relat_1(X1,X2))
    | r2_hidden(k4_tarski(esk1_3(X3,esk4_0,k5_relat_1(X1,X2)),esk2_3(X3,esk4_0,k5_relat_1(X1,X2))),esk4_0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( k5_relat_1(esk4_0,k6_relat_1(X1)) = k8_relat_1(X2,esk4_0)
    | r2_hidden(esk2_3(X2,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1))),X2)
    | r2_hidden(esk2_3(X2,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_9])])).

cnf(c_0_24,negated_conjecture,
    ( k5_relat_1(esk4_0,X1) = k8_relat_1(X2,esk4_0)
    | r2_hidden(k4_tarski(esk1_3(X2,esk4_0,k5_relat_1(esk4_0,X1)),esk2_3(X2,esk4_0,k5_relat_1(esk4_0,X1))),k5_relat_1(esk4_0,X1))
    | r2_hidden(k4_tarski(esk1_3(X2,esk4_0,k5_relat_1(esk4_0,X1)),esk2_3(X2,esk4_0,k5_relat_1(esk4_0,X1))),esk4_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_9])).

cnf(c_0_25,plain,
    ( X3 = k8_relat_1(X1,X2)
    | ~ r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_26,negated_conjecture,
    ( k5_relat_1(esk4_0,k6_relat_1(X1)) = k8_relat_1(X1,esk4_0)
    | r2_hidden(esk2_3(X1,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1))),X1) ),
    inference(ef,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,k6_relat_1(X4)))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( k5_relat_1(esk4_0,k6_relat_1(X1)) = k8_relat_1(X2,esk4_0)
    | r2_hidden(k4_tarski(esk1_3(X2,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1))),esk2_3(X2,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1)))),k5_relat_1(esk4_0,k6_relat_1(X1)))
    | r2_hidden(k4_tarski(esk1_3(X2,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1))),esk2_3(X2,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1)))),esk4_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( k5_relat_1(esk4_0,k6_relat_1(X1)) = k8_relat_1(X1,esk4_0)
    | ~ r2_hidden(k4_tarski(esk1_3(X1,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1))),esk2_3(X1,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1)))),k5_relat_1(esk4_0,k6_relat_1(X1)))
    | ~ r2_hidden(k4_tarski(esk1_3(X1,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1))),esk2_3(X1,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1)))),esk4_0)
    | ~ v1_relat_1(k5_relat_1(esk4_0,k6_relat_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_9])])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,k6_relat_1(X2)))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),X4)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( k5_relat_1(esk4_0,k6_relat_1(X1)) = k8_relat_1(X2,esk4_0)
    | r2_hidden(k4_tarski(esk1_3(X2,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1))),esk2_3(X2,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1)))),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_9])])).

cnf(c_0_32,negated_conjecture,
    ( k5_relat_1(esk4_0,k6_relat_1(X1)) = k8_relat_1(X1,esk4_0)
    | ~ r2_hidden(k4_tarski(esk1_3(X1,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1))),esk2_3(X1,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1)))),k5_relat_1(esk4_0,k6_relat_1(X1)))
    | ~ r2_hidden(k4_tarski(esk1_3(X1,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1))),esk2_3(X1,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1)))),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_12]),c_0_18]),c_0_9])])).

cnf(c_0_33,negated_conjecture,
    ( k5_relat_1(esk4_0,k6_relat_1(X1)) = k8_relat_1(X2,esk4_0)
    | r2_hidden(k4_tarski(esk1_3(X2,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1))),esk2_3(X2,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1)))),k5_relat_1(esk4_0,k6_relat_1(X3)))
    | ~ r2_hidden(esk2_3(X2,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1))),X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_9])])).

cnf(c_0_34,negated_conjecture,
    ( k5_relat_1(esk4_0,k6_relat_1(X1)) = k8_relat_1(X1,esk4_0)
    | ~ r2_hidden(k4_tarski(esk1_3(X1,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1))),esk2_3(X1,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1)))),k5_relat_1(esk4_0,k6_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( k8_relat_1(esk3_0,esk4_0) != k5_relat_1(esk4_0,k6_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_36,negated_conjecture,
    ( k5_relat_1(esk4_0,k6_relat_1(X1)) = k8_relat_1(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_26]),c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:01:12 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.54  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S080I
% 0.20/0.54  # and selection function SelectCQIArNXTEqFirst.
% 0.20/0.54  #
% 0.20/0.54  # Preprocessing time       : 0.027 s
% 0.20/0.54  # Presaturation interreduction done
% 0.20/0.54  
% 0.20/0.54  # Proof found!
% 0.20/0.54  # SZS status Theorem
% 0.20/0.54  # SZS output start CNFRefutation
% 0.20/0.54  fof(t123_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 0.20/0.54  fof(d12_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k8_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>(r2_hidden(X5,X1)&r2_hidden(k4_tarski(X4,X5),X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_relat_1)).
% 0.20/0.54  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.20/0.54  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.20/0.54  fof(t75_relat_1, axiom, ![X1, X2, X3, X4]:(v1_relat_1(X4)=>(r2_hidden(k4_tarski(X1,X2),k5_relat_1(X4,k6_relat_1(X3)))<=>(r2_hidden(X2,X3)&r2_hidden(k4_tarski(X1,X2),X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_relat_1)).
% 0.20/0.54  fof(c_0_5, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1)))), inference(assume_negation,[status(cth)],[t123_relat_1])).
% 0.20/0.54  fof(c_0_6, plain, ![X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X10,X6)|~r2_hidden(k4_tarski(X9,X10),X8)|X8!=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7))&(r2_hidden(k4_tarski(X9,X10),X7)|~r2_hidden(k4_tarski(X9,X10),X8)|X8!=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7)))&(~r2_hidden(X12,X6)|~r2_hidden(k4_tarski(X11,X12),X7)|r2_hidden(k4_tarski(X11,X12),X8)|X8!=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7)))&((~r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|(~r2_hidden(esk2_3(X6,X7,X8),X6)|~r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X7))|X8=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7))&((r2_hidden(esk2_3(X6,X7,X8),X6)|r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|X8=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7))&(r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X7)|r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|X8=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_1])])])])])])).
% 0.20/0.54  fof(c_0_7, negated_conjecture, (v1_relat_1(esk4_0)&k8_relat_1(esk3_0,esk4_0)!=k5_relat_1(esk4_0,k6_relat_1(esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.20/0.54  cnf(c_0_8, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X3)|X3=k8_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.54  cnf(c_0_9, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.54  fof(c_0_10, plain, ![X15, X16]:(~v1_relat_1(X15)|~v1_relat_1(X16)|v1_relat_1(k5_relat_1(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.20/0.54  cnf(c_0_11, negated_conjecture, (X1=k8_relat_1(X2,esk4_0)|r2_hidden(k4_tarski(esk1_3(X2,esk4_0,X1),esk2_3(X2,esk4_0,X1)),X1)|r2_hidden(esk2_3(X2,esk4_0,X1),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.20/0.54  cnf(c_0_12, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.54  cnf(c_0_13, negated_conjecture, (k5_relat_1(X1,X2)=k8_relat_1(X3,esk4_0)|r2_hidden(k4_tarski(esk1_3(X3,esk4_0,k5_relat_1(X1,X2)),esk2_3(X3,esk4_0,k5_relat_1(X1,X2))),k5_relat_1(X1,X2))|r2_hidden(esk2_3(X3,esk4_0,k5_relat_1(X1,X2)),X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.20/0.54  fof(c_0_14, plain, ![X17]:v1_relat_1(k6_relat_1(X17)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.20/0.54  cnf(c_0_15, plain, (r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X2)|r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X3)|X3=k8_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.54  fof(c_0_16, plain, ![X18, X19, X20, X21]:(((r2_hidden(X19,X20)|~r2_hidden(k4_tarski(X18,X19),k5_relat_1(X21,k6_relat_1(X20)))|~v1_relat_1(X21))&(r2_hidden(k4_tarski(X18,X19),X21)|~r2_hidden(k4_tarski(X18,X19),k5_relat_1(X21,k6_relat_1(X20)))|~v1_relat_1(X21)))&(~r2_hidden(X19,X20)|~r2_hidden(k4_tarski(X18,X19),X21)|r2_hidden(k4_tarski(X18,X19),k5_relat_1(X21,k6_relat_1(X20)))|~v1_relat_1(X21))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t75_relat_1])])])).
% 0.20/0.54  cnf(c_0_17, negated_conjecture, (k5_relat_1(esk4_0,X1)=k8_relat_1(X2,esk4_0)|r2_hidden(k4_tarski(esk1_3(X2,esk4_0,k5_relat_1(esk4_0,X1)),esk2_3(X2,esk4_0,k5_relat_1(esk4_0,X1))),k5_relat_1(esk4_0,X1))|r2_hidden(esk2_3(X2,esk4_0,k5_relat_1(esk4_0,X1)),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_13, c_0_9])).
% 0.20/0.54  cnf(c_0_18, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.54  cnf(c_0_19, negated_conjecture, (X1=k8_relat_1(X2,esk4_0)|r2_hidden(k4_tarski(esk1_3(X2,esk4_0,X1),esk2_3(X2,esk4_0,X1)),esk4_0)|r2_hidden(k4_tarski(esk1_3(X2,esk4_0,X1),esk2_3(X2,esk4_0,X1)),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_15, c_0_9])).
% 0.20/0.54  cnf(c_0_20, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,k6_relat_1(X2)))|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.54  cnf(c_0_21, negated_conjecture, (k5_relat_1(esk4_0,k6_relat_1(X1))=k8_relat_1(X2,esk4_0)|r2_hidden(k4_tarski(esk1_3(X2,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1))),esk2_3(X2,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1)))),k5_relat_1(esk4_0,k6_relat_1(X1)))|r2_hidden(esk2_3(X2,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1))),X2)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.54  cnf(c_0_22, negated_conjecture, (k5_relat_1(X1,X2)=k8_relat_1(X3,esk4_0)|r2_hidden(k4_tarski(esk1_3(X3,esk4_0,k5_relat_1(X1,X2)),esk2_3(X3,esk4_0,k5_relat_1(X1,X2))),k5_relat_1(X1,X2))|r2_hidden(k4_tarski(esk1_3(X3,esk4_0,k5_relat_1(X1,X2)),esk2_3(X3,esk4_0,k5_relat_1(X1,X2))),esk4_0)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_19, c_0_12])).
% 0.20/0.54  cnf(c_0_23, negated_conjecture, (k5_relat_1(esk4_0,k6_relat_1(X1))=k8_relat_1(X2,esk4_0)|r2_hidden(esk2_3(X2,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1))),X2)|r2_hidden(esk2_3(X2,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1))),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_9])])).
% 0.20/0.54  cnf(c_0_24, negated_conjecture, (k5_relat_1(esk4_0,X1)=k8_relat_1(X2,esk4_0)|r2_hidden(k4_tarski(esk1_3(X2,esk4_0,k5_relat_1(esk4_0,X1)),esk2_3(X2,esk4_0,k5_relat_1(esk4_0,X1))),k5_relat_1(esk4_0,X1))|r2_hidden(k4_tarski(esk1_3(X2,esk4_0,k5_relat_1(esk4_0,X1)),esk2_3(X2,esk4_0,k5_relat_1(esk4_0,X1))),esk4_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_9])).
% 0.20/0.54  cnf(c_0_25, plain, (X3=k8_relat_1(X1,X2)|~r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X2)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.54  cnf(c_0_26, negated_conjecture, (k5_relat_1(esk4_0,k6_relat_1(X1))=k8_relat_1(X1,esk4_0)|r2_hidden(esk2_3(X1,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1))),X1)), inference(ef,[status(thm)],[c_0_23])).
% 0.20/0.54  cnf(c_0_27, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,k6_relat_1(X4)))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.54  cnf(c_0_28, negated_conjecture, (k5_relat_1(esk4_0,k6_relat_1(X1))=k8_relat_1(X2,esk4_0)|r2_hidden(k4_tarski(esk1_3(X2,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1))),esk2_3(X2,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1)))),k5_relat_1(esk4_0,k6_relat_1(X1)))|r2_hidden(k4_tarski(esk1_3(X2,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1))),esk2_3(X2,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1)))),esk4_0)), inference(spm,[status(thm)],[c_0_24, c_0_18])).
% 0.20/0.54  cnf(c_0_29, negated_conjecture, (k5_relat_1(esk4_0,k6_relat_1(X1))=k8_relat_1(X1,esk4_0)|~r2_hidden(k4_tarski(esk1_3(X1,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1))),esk2_3(X1,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1)))),k5_relat_1(esk4_0,k6_relat_1(X1)))|~r2_hidden(k4_tarski(esk1_3(X1,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1))),esk2_3(X1,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1)))),esk4_0)|~v1_relat_1(k5_relat_1(esk4_0,k6_relat_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_9])])).
% 0.20/0.54  cnf(c_0_30, plain, (r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,k6_relat_1(X2)))|~r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),X4)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.54  cnf(c_0_31, negated_conjecture, (k5_relat_1(esk4_0,k6_relat_1(X1))=k8_relat_1(X2,esk4_0)|r2_hidden(k4_tarski(esk1_3(X2,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1))),esk2_3(X2,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1)))),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_9])])).
% 0.20/0.54  cnf(c_0_32, negated_conjecture, (k5_relat_1(esk4_0,k6_relat_1(X1))=k8_relat_1(X1,esk4_0)|~r2_hidden(k4_tarski(esk1_3(X1,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1))),esk2_3(X1,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1)))),k5_relat_1(esk4_0,k6_relat_1(X1)))|~r2_hidden(k4_tarski(esk1_3(X1,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1))),esk2_3(X1,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1)))),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_12]), c_0_18]), c_0_9])])).
% 0.20/0.54  cnf(c_0_33, negated_conjecture, (k5_relat_1(esk4_0,k6_relat_1(X1))=k8_relat_1(X2,esk4_0)|r2_hidden(k4_tarski(esk1_3(X2,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1))),esk2_3(X2,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1)))),k5_relat_1(esk4_0,k6_relat_1(X3)))|~r2_hidden(esk2_3(X2,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1))),X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_9])])).
% 0.20/0.54  cnf(c_0_34, negated_conjecture, (k5_relat_1(esk4_0,k6_relat_1(X1))=k8_relat_1(X1,esk4_0)|~r2_hidden(k4_tarski(esk1_3(X1,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1))),esk2_3(X1,esk4_0,k5_relat_1(esk4_0,k6_relat_1(X1)))),k5_relat_1(esk4_0,k6_relat_1(X1)))), inference(spm,[status(thm)],[c_0_32, c_0_31])).
% 0.20/0.54  cnf(c_0_35, negated_conjecture, (k8_relat_1(esk3_0,esk4_0)!=k5_relat_1(esk4_0,k6_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.54  cnf(c_0_36, negated_conjecture, (k5_relat_1(esk4_0,k6_relat_1(X1))=k8_relat_1(X1,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_26]), c_0_34])).
% 0.20/0.54  cnf(c_0_37, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36])]), ['proof']).
% 0.20/0.54  # SZS output end CNFRefutation
% 0.20/0.54  # Proof object total steps             : 38
% 0.20/0.54  # Proof object clause steps            : 27
% 0.20/0.54  # Proof object formula steps           : 11
% 0.20/0.54  # Proof object conjectures             : 22
% 0.20/0.54  # Proof object clause conjectures      : 19
% 0.20/0.54  # Proof object formula conjectures     : 3
% 0.20/0.54  # Proof object initial clauses used    : 10
% 0.20/0.54  # Proof object initial formulas used   : 5
% 0.20/0.54  # Proof object generating inferences   : 16
% 0.20/0.54  # Proof object simplifying inferences  : 14
% 0.20/0.54  # Training examples: 0 positive, 0 negative
% 0.20/0.54  # Parsed axioms                        : 5
% 0.20/0.54  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.54  # Initial clauses                      : 13
% 0.20/0.54  # Removed in clause preprocessing      : 0
% 0.20/0.54  # Initial clauses in saturation        : 13
% 0.20/0.54  # Processed clauses                    : 1168
% 0.20/0.54  # ...of these trivial                  : 0
% 0.20/0.54  # ...subsumed                          : 525
% 0.20/0.54  # ...remaining for further processing  : 643
% 0.20/0.54  # Other redundant clauses eliminated   : 3
% 0.20/0.54  # Clauses deleted for lack of memory   : 0
% 0.20/0.54  # Backward-subsumed                    : 47
% 0.20/0.54  # Backward-rewritten                   : 90
% 0.20/0.54  # Generated clauses                    : 2314
% 0.20/0.54  # ...of the previous two non-trivial   : 2398
% 0.20/0.54  # Contextual simplify-reflections      : 1
% 0.20/0.54  # Paramodulations                      : 2299
% 0.20/0.54  # Factorizations                       : 12
% 0.20/0.54  # Equation resolutions                 : 3
% 0.20/0.54  # Propositional unsat checks           : 0
% 0.20/0.54  #    Propositional check models        : 0
% 0.20/0.54  #    Propositional check unsatisfiable : 0
% 0.20/0.54  #    Propositional clauses             : 0
% 0.20/0.54  #    Propositional clauses after purity: 0
% 0.20/0.54  #    Propositional unsat core size     : 0
% 0.20/0.54  #    Propositional preprocessing time  : 0.000
% 0.20/0.54  #    Propositional encoding time       : 0.000
% 0.20/0.54  #    Propositional solver time         : 0.000
% 0.20/0.54  #    Success case prop preproc time    : 0.000
% 0.20/0.54  #    Success case prop encoding time   : 0.000
% 0.20/0.54  #    Success case prop solver time     : 0.000
% 0.20/0.54  # Current number of processed clauses  : 490
% 0.20/0.54  #    Positive orientable unit clauses  : 3
% 0.20/0.54  #    Positive unorientable unit clauses: 0
% 0.20/0.54  #    Negative unit clauses             : 0
% 0.20/0.54  #    Non-unit-clauses                  : 487
% 0.20/0.54  # Current number of unprocessed clauses: 1168
% 0.20/0.54  # ...number of literals in the above   : 6433
% 0.20/0.54  # Current number of archived formulas  : 0
% 0.20/0.54  # Current number of archived clauses   : 150
% 0.20/0.54  # Clause-clause subsumption calls (NU) : 322904
% 0.20/0.54  # Rec. Clause-clause subsumption calls : 7499
% 0.20/0.54  # Non-unit clause-clause subsumptions  : 573
% 0.20/0.54  # Unit Clause-clause subsumption calls : 487
% 0.20/0.54  # Rewrite failures with RHS unbound    : 0
% 0.20/0.54  # BW rewrite match attempts            : 5
% 0.20/0.54  # BW rewrite match successes           : 5
% 0.20/0.54  # Condensation attempts                : 0
% 0.20/0.54  # Condensation successes               : 0
% 0.20/0.54  # Termbank termtop insertions          : 119254
% 0.20/0.54  
% 0.20/0.54  # -------------------------------------------------
% 0.20/0.54  # User time                : 0.189 s
% 0.20/0.54  # System time              : 0.008 s
% 0.20/0.54  # Total time               : 0.197 s
% 0.20/0.54  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
