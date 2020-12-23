%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0938+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:26 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 114 expanded)
%              Number of clauses        :   32 (  53 expanded)
%              Number of leaves         :    6 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  180 ( 636 expanded)
%              Number of equality atoms :   19 (  62 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   33 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_wellord2,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k1_wellord2(X1)
      <=> ( k3_relat_1(X2) = X1
          & ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1) )
             => ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r1_tarski(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(d8_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r8_relat_2(X1,X2)
        <=> ! [X3,X4,X5] :
              ( ( r2_hidden(X3,X2)
                & r2_hidden(X4,X2)
                & r2_hidden(X5,X2)
                & r2_hidden(k4_tarski(X3,X4),X1)
                & r2_hidden(k4_tarski(X4,X5),X1) )
             => r2_hidden(k4_tarski(X3,X5),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_2)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(d16_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v8_relat_2(X1)
      <=> r8_relat_2(X1,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_2)).

fof(t3_wellord2,conjecture,(
    ! [X1] : v8_relat_2(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_wellord2)).

fof(c_0_6,plain,(
    ! [X7,X8,X9,X10] :
      ( ( k3_relat_1(X8) = X7
        | X8 != k1_wellord2(X7)
        | ~ v1_relat_1(X8) )
      & ( ~ r2_hidden(k4_tarski(X9,X10),X8)
        | r1_tarski(X9,X10)
        | ~ r2_hidden(X9,X7)
        | ~ r2_hidden(X10,X7)
        | X8 != k1_wellord2(X7)
        | ~ v1_relat_1(X8) )
      & ( ~ r1_tarski(X9,X10)
        | r2_hidden(k4_tarski(X9,X10),X8)
        | ~ r2_hidden(X9,X7)
        | ~ r2_hidden(X10,X7)
        | X8 != k1_wellord2(X7)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | k3_relat_1(X8) != X7
        | X8 = k1_wellord2(X7)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(esk2_2(X7,X8),X7)
        | k3_relat_1(X8) != X7
        | X8 = k1_wellord2(X7)
        | ~ v1_relat_1(X8) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X8)
        | ~ r1_tarski(esk1_2(X7,X8),esk2_2(X7,X8))
        | k3_relat_1(X8) != X7
        | X8 = k1_wellord2(X7)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X8)
        | r1_tarski(esk1_2(X7,X8),esk2_2(X7,X8))
        | k3_relat_1(X8) != X7
        | X8 = k1_wellord2(X7)
        | ~ v1_relat_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_7,plain,(
    ! [X22] : v1_relat_1(k1_wellord2(X22)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_8,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( ~ r8_relat_2(X13,X14)
        | ~ r2_hidden(X15,X14)
        | ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X17,X14)
        | ~ r2_hidden(k4_tarski(X15,X16),X13)
        | ~ r2_hidden(k4_tarski(X16,X17),X13)
        | r2_hidden(k4_tarski(X15,X17),X13)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(esk3_2(X13,X18),X18)
        | r8_relat_2(X13,X18)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(esk4_2(X13,X18),X18)
        | r8_relat_2(X13,X18)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(esk5_2(X13,X18),X18)
        | r8_relat_2(X13,X18)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(esk3_2(X13,X18),esk4_2(X13,X18)),X13)
        | r8_relat_2(X13,X18)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(esk4_2(X13,X18),esk5_2(X13,X18)),X13)
        | r8_relat_2(X13,X18)
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(k4_tarski(esk3_2(X13,X18),esk5_2(X13,X18)),X13)
        | r8_relat_2(X13,X18)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_2])])])])])])).

cnf(c_0_9,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X2,X4)
    | X3 != k1_wellord2(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)
    | r8_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_9]),c_0_10])])).

cnf(c_0_13,plain,
    ( r2_hidden(k4_tarski(esk4_2(k1_wellord2(X1),X2),esk5_2(k1_wellord2(X1),X2)),k1_wellord2(X1))
    | r8_relat_2(k1_wellord2(X1),X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(esk5_2(X1,X2),X2)
    | r8_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | r8_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)
    | r8_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_17,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(X23,X24)
      | ~ r1_tarski(X24,X25)
      | r1_tarski(X23,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_18,plain,
    ( r1_tarski(esk4_2(k1_wellord2(X1),X2),esk5_2(k1_wellord2(X1),X2))
    | r8_relat_2(k1_wellord2(X1),X2)
    | ~ r2_hidden(esk5_2(k1_wellord2(X1),X2),X1)
    | ~ r2_hidden(esk4_2(k1_wellord2(X1),X2),X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(esk5_2(k1_wellord2(X1),X2),X2)
    | r8_relat_2(k1_wellord2(X1),X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_10])).

cnf(c_0_20,plain,
    ( r2_hidden(esk4_2(k1_wellord2(X1),X2),X2)
    | r8_relat_2(k1_wellord2(X1),X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_10])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(esk3_2(k1_wellord2(X1),X2),esk4_2(k1_wellord2(X1),X2)),k1_wellord2(X1))
    | r8_relat_2(k1_wellord2(X1),X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_10])).

cnf(c_0_22,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r8_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X2,X4)
    | X3 != k1_wellord2(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r1_tarski(esk4_2(k1_wellord2(X1),X1),esk5_2(k1_wellord2(X1),X1))
    | r8_relat_2(k1_wellord2(X1),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_26,plain,
    ( r1_tarski(esk3_2(k1_wellord2(X1),X2),esk4_2(k1_wellord2(X1),X2))
    | r8_relat_2(k1_wellord2(X1),X2)
    | ~ r2_hidden(esk4_2(k1_wellord2(X1),X2),X1)
    | ~ r2_hidden(esk3_2(k1_wellord2(X1),X2),X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(esk3_2(k1_wellord2(X1),X2),X2)
    | r8_relat_2(k1_wellord2(X1),X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_10])).

fof(c_0_28,plain,(
    ! [X6] :
      ( ( ~ v8_relat_2(X6)
        | r8_relat_2(X6,k3_relat_1(X6))
        | ~ v1_relat_1(X6) )
      & ( ~ r8_relat_2(X6,k3_relat_1(X6))
        | v8_relat_2(X6)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_2])])])).

cnf(c_0_29,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_30,plain,
    ( r8_relat_2(X1,X2)
    | ~ r2_hidden(k4_tarski(esk3_2(X1,X2),esk5_2(X1,X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_31,plain,
    ( r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_23]),c_0_10])])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,esk5_2(k1_wellord2(X2),X2))
    | r8_relat_2(k1_wellord2(X2),X2)
    | ~ r1_tarski(X1,esk4_2(k1_wellord2(X2),X2)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( r1_tarski(esk3_2(k1_wellord2(X1),X1),esk4_2(k1_wellord2(X1),X1))
    | r8_relat_2(k1_wellord2(X1),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_20]),c_0_27])).

fof(c_0_34,negated_conjecture,(
    ~ ! [X1] : v8_relat_2(k1_wellord2(X1)) ),
    inference(assume_negation,[status(cth)],[t3_wellord2])).

cnf(c_0_35,plain,
    ( v8_relat_2(X1)
    | ~ r8_relat_2(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_29]),c_0_10])])).

cnf(c_0_37,plain,
    ( r8_relat_2(k1_wellord2(X1),X2)
    | ~ r1_tarski(esk3_2(k1_wellord2(X1),X2),esk5_2(k1_wellord2(X1),X2))
    | ~ r2_hidden(esk5_2(k1_wellord2(X1),X2),X1)
    | ~ r2_hidden(esk3_2(k1_wellord2(X1),X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_10])])).

cnf(c_0_38,plain,
    ( r1_tarski(esk3_2(k1_wellord2(X1),X1),esk5_2(k1_wellord2(X1),X1))
    | r8_relat_2(k1_wellord2(X1),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_39,negated_conjecture,(
    ~ v8_relat_2(k1_wellord2(esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_34])])])).

cnf(c_0_40,plain,
    ( v8_relat_2(k1_wellord2(X1))
    | ~ r8_relat_2(k1_wellord2(X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_10])])).

cnf(c_0_41,plain,
    ( r8_relat_2(k1_wellord2(X1),X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_27]),c_0_19])).

cnf(c_0_42,negated_conjecture,
    ( ~ v8_relat_2(k1_wellord2(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_43,plain,
    ( v8_relat_2(k1_wellord2(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41])])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43])]),
    [proof]).

%------------------------------------------------------------------------------
