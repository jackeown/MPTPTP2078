%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0477+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:41 EST 2020

% Result     : Theorem 0.08s
% Output     : CNFRefutation 0.08s
% Verified   : 
% Statistics : Number of formulae       :   31 ( 168 expanded)
%              Number of clauses        :   22 (  81 expanded)
%              Number of leaves         :    4 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  123 ( 776 expanded)
%              Number of equality atoms :   41 ( 238 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d7_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( X2 = k4_relat_1(X1)
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r2_hidden(k4_tarski(X4,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(d10_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k6_relat_1(X1)
      <=> ! [X3,X4] :
            ( r2_hidden(k4_tarski(X3,X4),X2)
          <=> ( r2_hidden(X3,X1)
              & X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).

fof(t72_relat_1,conjecture,(
    ! [X1] : k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

fof(c_0_4,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(k4_tarski(X15,X16),X14)
        | r2_hidden(k4_tarski(X16,X15),X13)
        | X14 != k4_relat_1(X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(k4_tarski(X18,X17),X13)
        | r2_hidden(k4_tarski(X17,X18),X14)
        | X14 != k4_relat_1(X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(k4_tarski(esk3_2(X13,X14),esk4_2(X13,X14)),X14)
        | ~ r2_hidden(k4_tarski(esk4_2(X13,X14),esk3_2(X13,X14)),X13)
        | X14 = k4_relat_1(X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(esk3_2(X13,X14),esk4_2(X13,X14)),X14)
        | r2_hidden(k4_tarski(esk4_2(X13,X14),esk3_2(X13,X14)),X13)
        | X14 = k4_relat_1(X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_relat_1])])])])])])).

fof(c_0_5,plain,(
    ! [X21] : v1_relat_1(k6_relat_1(X21)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( r2_hidden(X7,X5)
        | ~ r2_hidden(k4_tarski(X7,X8),X6)
        | X6 != k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( X7 = X8
        | ~ r2_hidden(k4_tarski(X7,X8),X6)
        | X6 != k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(X9,X5)
        | X9 != X10
        | r2_hidden(k4_tarski(X9,X10),X6)
        | X6 != k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | ~ r2_hidden(esk1_2(X5,X6),X5)
        | esk1_2(X5,X6) != esk2_2(X5,X6)
        | X6 = k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk1_2(X5,X6),X5)
        | r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | X6 = k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( esk1_2(X5,X6) = esk2_2(X5,X6)
        | r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | X6 = k6_relat_1(X5)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_relat_1])])])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X2)
    | r2_hidden(k4_tarski(esk4_2(X1,X2),esk3_2(X1,X2)),X1)
    | X2 = k4_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X3 != k6_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k6_relat_1(X1) = k4_relat_1(X2)
    | r2_hidden(k4_tarski(esk3_2(X2,k6_relat_1(X1)),esk4_2(X2,k6_relat_1(X1))),k6_relat_1(X1))
    | r2_hidden(k4_tarski(esk4_2(X2,k6_relat_1(X1)),esk3_2(X2,k6_relat_1(X1))),X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X4 != k6_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X2),k6_relat_1(X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_9]),c_0_8])])).

cnf(c_0_13,plain,
    ( k6_relat_1(X1) = k4_relat_1(k6_relat_1(X2))
    | r2_hidden(k4_tarski(esk4_2(k6_relat_1(X2),k6_relat_1(X1)),esk3_2(k6_relat_1(X2),k6_relat_1(X1))),k6_relat_1(X2))
    | r2_hidden(k4_tarski(esk3_2(k6_relat_1(X2),k6_relat_1(X1)),esk4_2(k6_relat_1(X2),k6_relat_1(X1))),k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_8])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_8])])).

cnf(c_0_15,plain,
    ( X2 = k4_relat_1(X1)
    | ~ r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X2)
    | ~ r2_hidden(k4_tarski(esk4_2(X1,X2),esk3_2(X1,X2)),X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_16,plain,
    ( esk4_2(k6_relat_1(X1),k6_relat_1(X2)) = esk3_2(k6_relat_1(X1),k6_relat_1(X2))
    | k6_relat_1(X2) = k4_relat_1(k6_relat_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(X1,X3),X4)
    | ~ r2_hidden(X1,X2)
    | X1 != X3
    | X4 != k6_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,plain,
    ( k6_relat_1(X1) = k4_relat_1(k6_relat_1(X2))
    | r2_hidden(k4_tarski(esk4_2(k6_relat_1(X2),k6_relat_1(X1)),esk3_2(k6_relat_1(X2),k6_relat_1(X1))),k6_relat_1(X2))
    | r2_hidden(esk3_2(k6_relat_1(X2),k6_relat_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_13])).

cnf(c_0_19,plain,
    ( k6_relat_1(X1) = k4_relat_1(k6_relat_1(X2))
    | ~ r2_hidden(k4_tarski(esk3_2(k6_relat_1(X2),k6_relat_1(X1)),esk3_2(k6_relat_1(X2),k6_relat_1(X1))),k6_relat_1(X1))
    | ~ r2_hidden(k4_tarski(esk3_2(k6_relat_1(X2),k6_relat_1(X1)),esk3_2(k6_relat_1(X2),k6_relat_1(X1))),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_8]),c_0_8])])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(X1,X1),k6_relat_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_17])]),c_0_8])])).

cnf(c_0_21,plain,
    ( k6_relat_1(X1) = k4_relat_1(k6_relat_1(X2))
    | r2_hidden(esk3_2(k6_relat_1(X2),k6_relat_1(X1)),X1)
    | r2_hidden(esk4_2(k6_relat_1(X2),k6_relat_1(X1)),X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_18])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1] : k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(assume_negation,[status(cth)],[t72_relat_1])).

cnf(c_0_23,plain,
    ( k6_relat_1(X1) = k4_relat_1(k6_relat_1(X2))
    | ~ r2_hidden(k4_tarski(esk3_2(k6_relat_1(X2),k6_relat_1(X1)),esk3_2(k6_relat_1(X2),k6_relat_1(X1))),k6_relat_1(X2))
    | ~ r2_hidden(esk3_2(k6_relat_1(X2),k6_relat_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( k6_relat_1(X1) = k4_relat_1(k6_relat_1(X2))
    | r2_hidden(esk3_2(k6_relat_1(X2),k6_relat_1(X1)),X2)
    | r2_hidden(esk3_2(k6_relat_1(X2),k6_relat_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_16])).

fof(c_0_25,negated_conjecture,(
    k4_relat_1(k6_relat_1(esk5_0)) != k6_relat_1(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

cnf(c_0_26,plain,
    ( k6_relat_1(X1) = k4_relat_1(k6_relat_1(X2))
    | ~ r2_hidden(esk3_2(k6_relat_1(X2),k6_relat_1(X1)),X1)
    | ~ r2_hidden(esk3_2(k6_relat_1(X2),k6_relat_1(X1)),X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_20])).

cnf(c_0_27,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1)
    | r2_hidden(esk3_2(k6_relat_1(X1),k6_relat_1(X1)),X1) ),
    inference(ef,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( k4_relat_1(k6_relat_1(esk5_0)) != k6_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29])]),
    [proof]).

%------------------------------------------------------------------------------
