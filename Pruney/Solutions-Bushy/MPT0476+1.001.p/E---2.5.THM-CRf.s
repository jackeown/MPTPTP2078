%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0476+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:41 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 214 expanded)
%              Number of clauses        :   27 ( 107 expanded)
%              Number of leaves         :    5 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :  136 (1104 expanded)
%              Number of equality atoms :   56 ( 393 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   26 (   2 average)
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

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(t71_relat_1,conjecture,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(c_0_5,plain,(
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

fof(c_0_6,plain,(
    ! [X35] : v1_relat_1(k6_relat_1(X35)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_7,plain,(
    ! [X24,X25,X26,X28,X29,X30,X31,X33] :
      ( ( ~ r2_hidden(X26,X25)
        | r2_hidden(k4_tarski(esk6_3(X24,X25,X26),X26),X24)
        | X25 != k2_relat_1(X24) )
      & ( ~ r2_hidden(k4_tarski(X29,X28),X24)
        | r2_hidden(X28,X25)
        | X25 != k2_relat_1(X24) )
      & ( ~ r2_hidden(esk7_2(X30,X31),X31)
        | ~ r2_hidden(k4_tarski(X33,esk7_2(X30,X31)),X30)
        | X31 = k2_relat_1(X30) )
      & ( r2_hidden(esk7_2(X30,X31),X31)
        | r2_hidden(k4_tarski(esk8_2(X30,X31),esk7_2(X30,X31)),X30)
        | X31 = k2_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_8,plain,
    ( r2_hidden(k4_tarski(X1,X3),X4)
    | ~ r2_hidden(X1,X2)
    | X1 != X3
    | X4 != k6_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X3 != k6_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X4 != k6_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_12,plain,(
    ! [X13,X14,X15,X17,X18,X19,X20,X22] :
      ( ( ~ r2_hidden(X15,X14)
        | r2_hidden(k4_tarski(X15,esk3_3(X13,X14,X15)),X13)
        | X14 != k1_relat_1(X13) )
      & ( ~ r2_hidden(k4_tarski(X17,X18),X13)
        | r2_hidden(X17,X14)
        | X14 != k1_relat_1(X13) )
      & ( ~ r2_hidden(esk4_2(X19,X20),X20)
        | ~ r2_hidden(k4_tarski(esk4_2(X19,X20),X22),X19)
        | X20 = k1_relat_1(X19) )
      & ( r2_hidden(esk4_2(X19,X20),X20)
        | r2_hidden(k4_tarski(esk4_2(X19,X20),esk5_2(X19,X20)),X19)
        | X20 = k1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_13,plain,
    ( X2 = k2_relat_1(X1)
    | ~ r2_hidden(esk7_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(X3,esk7_2(X1,X2)),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,X1),k6_relat_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_8])]),c_0_9])])).

cnf(c_0_15,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X2),k6_relat_1(X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_10]),c_0_9])])).

cnf(c_0_16,plain,
    ( r2_hidden(esk7_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk8_2(X1,X2),esk7_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_9])])).

cnf(c_0_18,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)
    | X2 = k1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( X1 = k2_relat_1(k6_relat_1(X2))
    | ~ r2_hidden(esk7_2(k6_relat_1(X2),X1),X1)
    | ~ r2_hidden(esk7_2(k6_relat_1(X2),X1),X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,plain,
    ( esk8_2(k6_relat_1(X1),X2) = esk7_2(k6_relat_1(X1),X2)
    | X2 = k2_relat_1(k6_relat_1(X1))
    | r2_hidden(esk7_2(k6_relat_1(X1),X2),X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( X2 = k1_relat_1(X1)
    | ~ r2_hidden(esk4_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(esk4_2(X1,X2),X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( X1 = k1_relat_1(k6_relat_1(X2))
    | r2_hidden(esk4_2(k6_relat_1(X2),X1),X1)
    | r2_hidden(esk4_2(k6_relat_1(X2),X1),X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1] :
        ( k1_relat_1(k6_relat_1(X1)) = X1
        & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    inference(assume_negation,[status(cth)],[t71_relat_1])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( esk8_2(k6_relat_1(X1),X2) = esk7_2(k6_relat_1(X1),X2)
    | X2 = k2_relat_1(k6_relat_1(X1))
    | ~ r2_hidden(esk7_2(k6_relat_1(X1),X2),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( X1 = k1_relat_1(k6_relat_1(X2))
    | ~ r2_hidden(esk4_2(k6_relat_1(X2),X1),X1)
    | ~ r2_hidden(esk4_2(k6_relat_1(X2),X1),X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_14])).

cnf(c_0_28,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1
    | r2_hidden(esk4_2(k6_relat_1(X1),X1),X1) ),
    inference(ef,[status(thm)],[c_0_23])).

fof(c_0_29,negated_conjecture,
    ( k1_relat_1(k6_relat_1(esk9_0)) != esk9_0
    | k2_relat_1(k6_relat_1(esk9_0)) != esk9_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

cnf(c_0_30,plain,
    ( X1 = k2_relat_1(X2)
    | r2_hidden(esk8_2(X2,X1),k1_relat_1(X2))
    | r2_hidden(esk7_2(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_16])).

cnf(c_0_31,plain,
    ( esk8_2(k6_relat_1(X1),X1) = esk7_2(k6_relat_1(X1),X1)
    | k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_26,c_0_21])).

cnf(c_0_32,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( k1_relat_1(k6_relat_1(esk9_0)) != esk9_0
    | k2_relat_1(k6_relat_1(esk9_0)) != esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1
    | r2_hidden(esk7_2(k6_relat_1(X1),X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_35,negated_conjecture,
    ( k2_relat_1(k6_relat_1(esk9_0)) != esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_32])])).

cnf(c_0_36,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_34]),c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])]),
    [proof]).

%------------------------------------------------------------------------------
