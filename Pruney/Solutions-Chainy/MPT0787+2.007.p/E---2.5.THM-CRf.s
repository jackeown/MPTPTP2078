%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:56 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  103 (4038 expanded)
%              Number of clauses        :   84 (1623 expanded)
%              Number of leaves         :    9 ( 939 expanded)
%              Depth                    :   48
%              Number of atoms          :  531 (25906 expanded)
%              Number of equality atoms :   95 (3088 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   51 (   4 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_wellord1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).

fof(d4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
      <=> ( v1_relat_2(X1)
          & v8_relat_2(X1)
          & v4_relat_2(X1)
          & v6_relat_2(X1)
          & v1_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

fof(d1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k1_wellord1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( X4 != X2
                & r2_hidden(k4_tarski(X4,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(l2_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v8_relat_2(X1)
      <=> ! [X2,X3,X4] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
              & r2_hidden(k4_tarski(X3,X4),X1) )
           => r2_hidden(k4_tarski(X2,X4),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_wellord1)).

fof(t30_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

fof(t36_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( ( v2_wellord1(X2)
          & r1_tarski(X1,k3_relat_1(X2)) )
       => ( ~ ( X1 != k3_relat_1(X2)
              & ! [X3] :
                  ~ ( r2_hidden(X3,k3_relat_1(X2))
                    & X1 = k1_wellord1(X2,X3) ) )
        <=> ! [X3] :
              ( r2_hidden(X3,X1)
             => ! [X4] :
                  ( r2_hidden(k4_tarski(X4,X3),X2)
                 => r2_hidden(X4,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_wellord1)).

fof(l1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
      <=> ! [X2] :
            ( r2_hidden(X2,k3_relat_1(X1))
           => r2_hidden(k4_tarski(X2,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_wellord1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( ( v2_wellord1(X3)
            & r2_hidden(X1,k3_relat_1(X3))
            & r2_hidden(X2,k3_relat_1(X3)) )
         => ( r2_hidden(k4_tarski(X1,X2),X3)
          <=> r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t37_wellord1])).

fof(c_0_10,plain,(
    ! [X33,X34,X35] :
      ( ( ~ v6_relat_2(X33)
        | ~ r2_hidden(X34,k3_relat_1(X33))
        | ~ r2_hidden(X35,k3_relat_1(X33))
        | X34 = X35
        | r2_hidden(k4_tarski(X34,X35),X33)
        | r2_hidden(k4_tarski(X35,X34),X33)
        | ~ v1_relat_1(X33) )
      & ( r2_hidden(esk7_1(X33),k3_relat_1(X33))
        | v6_relat_2(X33)
        | ~ v1_relat_1(X33) )
      & ( r2_hidden(esk8_1(X33),k3_relat_1(X33))
        | v6_relat_2(X33)
        | ~ v1_relat_1(X33) )
      & ( esk7_1(X33) != esk8_1(X33)
        | v6_relat_2(X33)
        | ~ v1_relat_1(X33) )
      & ( ~ r2_hidden(k4_tarski(esk7_1(X33),esk8_1(X33)),X33)
        | v6_relat_2(X33)
        | ~ v1_relat_1(X33) )
      & ( ~ r2_hidden(k4_tarski(esk8_1(X33),esk7_1(X33)),X33)
        | v6_relat_2(X33)
        | ~ v1_relat_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).

fof(c_0_11,negated_conjecture,
    ( v1_relat_1(esk14_0)
    & v2_wellord1(esk14_0)
    & r2_hidden(esk12_0,k3_relat_1(esk14_0))
    & r2_hidden(esk13_0,k3_relat_1(esk14_0))
    & ( ~ r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)
      | ~ r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0)) )
    & ( r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)
      | r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_12,plain,
    ( X2 = X3
    | r2_hidden(k4_tarski(X2,X3),X1)
    | r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v6_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(X3,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk13_0,k3_relat_1(esk14_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk14_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X22] :
      ( ( v1_relat_2(X22)
        | ~ v2_wellord1(X22)
        | ~ v1_relat_1(X22) )
      & ( v8_relat_2(X22)
        | ~ v2_wellord1(X22)
        | ~ v1_relat_1(X22) )
      & ( v4_relat_2(X22)
        | ~ v2_wellord1(X22)
        | ~ v1_relat_1(X22) )
      & ( v6_relat_2(X22)
        | ~ v2_wellord1(X22)
        | ~ v1_relat_1(X22) )
      & ( v1_wellord1(X22)
        | ~ v2_wellord1(X22)
        | ~ v1_relat_1(X22) )
      & ( ~ v1_relat_2(X22)
        | ~ v8_relat_2(X22)
        | ~ v4_relat_2(X22)
        | ~ v6_relat_2(X22)
        | ~ v1_wellord1(X22)
        | v2_wellord1(X22)
        | ~ v1_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

fof(c_0_16,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20] :
      ( ( X17 != X15
        | ~ r2_hidden(X17,X16)
        | X16 != k1_wellord1(X14,X15)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(k4_tarski(X17,X15),X14)
        | ~ r2_hidden(X17,X16)
        | X16 != k1_wellord1(X14,X15)
        | ~ v1_relat_1(X14) )
      & ( X18 = X15
        | ~ r2_hidden(k4_tarski(X18,X15),X14)
        | r2_hidden(X18,X16)
        | X16 != k1_wellord1(X14,X15)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(esk2_3(X14,X19,X20),X20)
        | esk2_3(X14,X19,X20) = X19
        | ~ r2_hidden(k4_tarski(esk2_3(X14,X19,X20),X19),X14)
        | X20 = k1_wellord1(X14,X19)
        | ~ v1_relat_1(X14) )
      & ( esk2_3(X14,X19,X20) != X19
        | r2_hidden(esk2_3(X14,X19,X20),X20)
        | X20 = k1_wellord1(X14,X19)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(k4_tarski(esk2_3(X14,X19,X20),X19),X14)
        | r2_hidden(esk2_3(X14,X19,X20),X20)
        | X20 = k1_wellord1(X14,X19)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).

cnf(c_0_17,negated_conjecture,
    ( X1 = esk13_0
    | r2_hidden(k4_tarski(esk13_0,X1),esk14_0)
    | r2_hidden(k4_tarski(X1,esk13_0),esk14_0)
    | ~ v6_relat_2(esk14_0)
    | ~ r2_hidden(X1,k3_relat_1(esk14_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])])).

cnf(c_0_18,plain,
    ( v6_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( v2_wellord1(esk14_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( X1 = X2
    | r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( X1 = esk13_0
    | r2_hidden(k4_tarski(X1,esk13_0),esk14_0)
    | r2_hidden(k4_tarski(esk13_0,X1),esk14_0)
    | ~ r2_hidden(X1,k3_relat_1(esk14_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_14])])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk12_0,k3_relat_1(esk14_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_23,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_24,plain,
    ( X1 = X2
    | r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X3) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk13_0,esk12_0),esk14_0)
    | r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_26,plain,(
    ! [X26,X27,X28,X29] :
      ( ( ~ v8_relat_2(X26)
        | ~ r2_hidden(k4_tarski(X27,X28),X26)
        | ~ r2_hidden(k4_tarski(X28,X29),X26)
        | r2_hidden(k4_tarski(X27,X29),X26)
        | ~ v1_relat_1(X26) )
      & ( r2_hidden(k4_tarski(esk4_1(X26),esk5_1(X26)),X26)
        | v8_relat_2(X26)
        | ~ v1_relat_1(X26) )
      & ( r2_hidden(k4_tarski(esk5_1(X26),esk6_1(X26)),X26)
        | v8_relat_2(X26)
        | ~ v1_relat_1(X26) )
      & ( ~ r2_hidden(k4_tarski(esk4_1(X26),esk6_1(X26)),X26)
        | v8_relat_2(X26)
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l2_wellord1])])])])])).

cnf(c_0_27,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)
    | r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_14])])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X2,X4),X1)
    | ~ v8_relat_2(X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X1)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)
    | r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))
    | ~ r2_hidden(X1,k1_wellord1(esk14_0,esk12_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))
    | r2_hidden(esk12_0,k1_wellord1(esk14_0,esk13_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_29]),c_0_14])])).

cnf(c_0_34,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)
    | r2_hidden(k4_tarski(X1,esk12_0),esk14_0)
    | ~ v8_relat_2(esk14_0)
    | ~ r2_hidden(k4_tarski(X1,esk13_0),esk14_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_25]),c_0_14])])).

cnf(c_0_35,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k1_wellord1(X3,X2)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_36,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,X3)
    | X3 != k1_wellord1(X4,X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_37,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(esk12_0,k1_wellord1(esk14_0,esk13_0))
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk13_0))
    | r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)
    | r2_hidden(k4_tarski(X1,esk12_0),esk14_0)
    | ~ v8_relat_2(esk14_0)
    | ~ r2_hidden(X1,k1_wellord1(esk14_0,esk13_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_14])])).

cnf(c_0_39,plain,
    ( v8_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_40,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_wellord1(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_36])])).

cnf(c_0_41,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk13_0))
    | r2_hidden(esk12_0,k1_wellord1(esk14_0,esk13_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_37]),c_0_14])])).

cnf(c_0_42,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)
    | r2_hidden(k4_tarski(X1,esk12_0),esk14_0)
    | ~ r2_hidden(X1,k1_wellord1(esk14_0,esk13_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_19]),c_0_14])])).

cnf(c_0_43,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(esk12_0,k1_wellord1(esk14_0,esk13_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_14])])).

cnf(c_0_44,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)
    | r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_45,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)
    | r2_hidden(k4_tarski(X1,esk13_0),esk14_0)
    | ~ v8_relat_2(esk14_0)
    | ~ r2_hidden(k4_tarski(X1,esk12_0),esk14_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_44]),c_0_14])])).

cnf(c_0_46,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)
    | r2_hidden(k4_tarski(X1,esk13_0),esk14_0)
    | ~ r2_hidden(k4_tarski(X1,esk12_0),esk14_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_39]),c_0_19]),c_0_14])])).

fof(c_0_47,plain,(
    ! [X11,X12,X13] :
      ( ( r2_hidden(X11,k3_relat_1(X13))
        | ~ r2_hidden(k4_tarski(X11,X12),X13)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(X12,k3_relat_1(X13))
        | ~ r2_hidden(k4_tarski(X11,X12),X13)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).

cnf(c_0_48,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)
    | r2_hidden(k4_tarski(X1,esk13_0),esk14_0)
    | ~ r2_hidden(X1,k1_wellord1(esk14_0,esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_35]),c_0_14])])).

cnf(c_0_49,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_50,plain,(
    ! [X38,X39,X40,X41,X42] :
      ( ( X38 != k3_relat_1(X39)
        | ~ r2_hidden(X41,X38)
        | ~ r2_hidden(k4_tarski(X42,X41),X39)
        | r2_hidden(X42,X38)
        | ~ v2_wellord1(X39)
        | ~ r1_tarski(X38,k3_relat_1(X39))
        | ~ v1_relat_1(X39) )
      & ( ~ r2_hidden(X40,k3_relat_1(X39))
        | X38 != k1_wellord1(X39,X40)
        | ~ r2_hidden(X41,X38)
        | ~ r2_hidden(k4_tarski(X42,X41),X39)
        | r2_hidden(X42,X38)
        | ~ v2_wellord1(X39)
        | ~ r1_tarski(X38,k3_relat_1(X39))
        | ~ v1_relat_1(X39) )
      & ( r2_hidden(esk11_2(X38,X39),k3_relat_1(X39))
        | X38 = k3_relat_1(X39)
        | r2_hidden(esk9_2(X38,X39),X38)
        | ~ v2_wellord1(X39)
        | ~ r1_tarski(X38,k3_relat_1(X39))
        | ~ v1_relat_1(X39) )
      & ( X38 = k1_wellord1(X39,esk11_2(X38,X39))
        | X38 = k3_relat_1(X39)
        | r2_hidden(esk9_2(X38,X39),X38)
        | ~ v2_wellord1(X39)
        | ~ r1_tarski(X38,k3_relat_1(X39))
        | ~ v1_relat_1(X39) )
      & ( r2_hidden(esk11_2(X38,X39),k3_relat_1(X39))
        | X38 = k3_relat_1(X39)
        | r2_hidden(k4_tarski(esk10_2(X38,X39),esk9_2(X38,X39)),X39)
        | ~ v2_wellord1(X39)
        | ~ r1_tarski(X38,k3_relat_1(X39))
        | ~ v1_relat_1(X39) )
      & ( X38 = k1_wellord1(X39,esk11_2(X38,X39))
        | X38 = k3_relat_1(X39)
        | r2_hidden(k4_tarski(esk10_2(X38,X39),esk9_2(X38,X39)),X39)
        | ~ v2_wellord1(X39)
        | ~ r1_tarski(X38,k3_relat_1(X39))
        | ~ v1_relat_1(X39) )
      & ( r2_hidden(esk11_2(X38,X39),k3_relat_1(X39))
        | X38 = k3_relat_1(X39)
        | ~ r2_hidden(esk10_2(X38,X39),X38)
        | ~ v2_wellord1(X39)
        | ~ r1_tarski(X38,k3_relat_1(X39))
        | ~ v1_relat_1(X39) )
      & ( X38 = k1_wellord1(X39,esk11_2(X38,X39))
        | X38 = k3_relat_1(X39)
        | ~ r2_hidden(esk10_2(X38,X39),X38)
        | ~ v2_wellord1(X39)
        | ~ r1_tarski(X38,k3_relat_1(X39))
        | ~ v1_relat_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_wellord1])])])])])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk1_2(k1_wellord1(esk14_0,esk12_0),X1),esk13_0),esk14_0)
    | r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)
    | r1_tarski(k1_wellord1(esk14_0,esk12_0),X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,plain,
    ( r2_hidden(X5,X3)
    | ~ r2_hidden(X1,k3_relat_1(X2))
    | X3 != k1_wellord1(X2,X1)
    | ~ r2_hidden(X4,X3)
    | ~ r2_hidden(k4_tarski(X5,X4),X2)
    | ~ v2_wellord1(X2)
    | ~ r1_tarski(X3,k3_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_55,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(esk1_2(k1_wellord1(esk14_0,esk12_0),X1),k3_relat_1(esk14_0))
    | r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)
    | r1_tarski(k1_wellord1(esk14_0,esk12_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_14])])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,k1_wellord1(X2,X3))
    | ~ v2_wellord1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,k1_wellord1(X2,X3))
    | ~ r2_hidden(X3,k3_relat_1(X2))
    | ~ r1_tarski(k1_wellord1(X2,X3),k3_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)
    | r1_tarski(k1_wellord1(esk14_0,esk12_0),k3_relat_1(esk14_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)
    | r2_hidden(X1,k1_wellord1(esk14_0,esk12_0))
    | ~ r2_hidden(X2,k1_wellord1(esk14_0,esk12_0))
    | ~ r2_hidden(k4_tarski(X1,X2),esk14_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_19]),c_0_14]),c_0_22])])).

cnf(c_0_59,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)
    | r2_hidden(X1,k1_wellord1(esk14_0,esk12_0))
    | ~ r2_hidden(X2,k1_wellord1(esk14_0,esk12_0))
    | ~ r2_hidden(X1,k1_wellord1(esk14_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_35]),c_0_14])])).

cnf(c_0_60,negated_conjecture,
    ( esk1_2(k1_wellord1(esk14_0,esk12_0),X1) = esk13_0
    | esk13_0 = esk12_0
    | r2_hidden(esk1_2(k1_wellord1(esk14_0,esk12_0),X1),k1_wellord1(esk14_0,esk13_0))
    | r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)
    | r1_tarski(k1_wellord1(esk14_0,esk12_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_52]),c_0_14])])).

cnf(c_0_61,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)
    | r2_hidden(X1,k1_wellord1(esk14_0,esk12_0))
    | r1_tarski(k1_wellord1(esk14_0,esk12_0),X2)
    | ~ r2_hidden(X1,k1_wellord1(esk14_0,esk1_2(k1_wellord1(esk14_0,esk12_0),X2))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_49])).

cnf(c_0_62,negated_conjecture,
    ( esk1_2(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0)) = esk13_0
    | esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)
    | r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)
    | r2_hidden(X1,k1_wellord1(esk14_0,esk12_0))
    | r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0))
    | ~ r2_hidden(X1,k1_wellord1(esk14_0,esk13_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_wellord1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_35])).

cnf(c_0_65,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(esk1_2(k1_wellord1(esk14_0,esk13_0),X1),k1_wellord1(esk14_0,esk12_0))
    | r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)
    | r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0))
    | r1_tarski(k1_wellord1(esk14_0,esk13_0),X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_49])).

cnf(c_0_66,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(esk1_2(k1_wellord1(esk14_0,esk13_0),X1),k3_relat_1(esk14_0))
    | r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)
    | r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0))
    | r1_tarski(k1_wellord1(esk14_0,esk13_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_14])])).

cnf(c_0_67,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)
    | ~ r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_68,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)
    | r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0))
    | r1_tarski(k1_wellord1(esk14_0,esk13_0),k3_relat_1(esk14_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)
    | r1_tarski(k1_wellord1(esk14_0,esk13_0),k3_relat_1(esk14_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_44])).

cnf(c_0_70,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)
    | r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))
    | ~ r2_hidden(X2,k1_wellord1(esk14_0,esk13_0))
    | ~ r2_hidden(k4_tarski(X1,X2),esk14_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_69]),c_0_19]),c_0_14]),c_0_13])])).

cnf(c_0_71,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)
    | r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))
    | ~ r2_hidden(X2,k1_wellord1(esk14_0,esk13_0))
    | ~ r2_hidden(X1,k1_wellord1(esk14_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_35]),c_0_14])])).

cnf(c_0_72,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)
    | r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))
    | ~ r2_hidden(X1,k1_wellord1(esk14_0,esk12_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_43])).

cnf(c_0_73,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(esk1_2(k1_wellord1(esk14_0,esk12_0),X1),k1_wellord1(esk14_0,esk13_0))
    | r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)
    | r1_tarski(k1_wellord1(esk14_0,esk12_0),X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_49])).

cnf(c_0_74,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)
    | r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_73])).

cnf(c_0_75,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v8_relat_2(X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X4),X3)
    | ~ r2_hidden(X4,k1_wellord1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_35])).

cnf(c_0_76,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_74]),c_0_44])).

cnf(c_0_77,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,X1),esk14_0)
    | ~ v8_relat_2(esk14_0)
    | ~ r2_hidden(esk12_0,k1_wellord1(esk14_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_14])])).

cnf(c_0_78,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(X1,X2),esk14_0)
    | ~ v8_relat_2(esk14_0)
    | ~ r2_hidden(k4_tarski(X1,esk12_0),esk14_0)
    | ~ r2_hidden(esk12_0,k1_wellord1(esk14_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_77]),c_0_14])])).

cnf(c_0_79,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(X1,X2),esk14_0)
    | ~ v8_relat_2(esk14_0)
    | ~ r2_hidden(esk12_0,k1_wellord1(esk14_0,X2))
    | ~ r2_hidden(X1,k1_wellord1(esk14_0,esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_35]),c_0_14])])).

cnf(c_0_80,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(X1,k3_relat_1(esk14_0))
    | ~ v8_relat_2(esk14_0)
    | ~ r2_hidden(esk12_0,k1_wellord1(esk14_0,X2))
    | ~ r2_hidden(X1,k1_wellord1(esk14_0,esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_79]),c_0_14])])).

cnf(c_0_81,negated_conjecture,
    ( esk13_0 = esk12_0
    | X1 = X2
    | r2_hidden(X1,k1_wellord1(esk14_0,X2))
    | ~ v8_relat_2(esk14_0)
    | ~ r2_hidden(esk12_0,k1_wellord1(esk14_0,X2))
    | ~ r2_hidden(X1,k1_wellord1(esk14_0,esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_79]),c_0_14])])).

cnf(c_0_82,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(X1,k3_relat_1(esk14_0))
    | ~ v8_relat_2(esk14_0)
    | ~ r2_hidden(X1,k1_wellord1(esk14_0,esk12_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_43])).

cnf(c_0_83,negated_conjecture,
    ( esk13_0 = esk12_0
    | X1 = esk13_0
    | r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))
    | ~ v8_relat_2(esk14_0)
    | ~ r2_hidden(X1,k1_wellord1(esk14_0,esk12_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_43])).

cnf(c_0_84,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(esk1_2(k1_wellord1(esk14_0,esk12_0),X1),k3_relat_1(esk14_0))
    | r1_tarski(k1_wellord1(esk14_0,esk12_0),X1)
    | ~ v8_relat_2(esk14_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_49])).

cnf(c_0_85,negated_conjecture,
    ( esk1_2(X1,k1_wellord1(esk14_0,esk13_0)) = esk13_0
    | esk13_0 = esk12_0
    | r1_tarski(X1,k1_wellord1(esk14_0,esk13_0))
    | ~ v8_relat_2(esk14_0)
    | ~ r2_hidden(esk1_2(X1,k1_wellord1(esk14_0,esk13_0)),k1_wellord1(esk14_0,esk12_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( esk13_0 = esk12_0
    | r1_tarski(k1_wellord1(esk14_0,esk12_0),k3_relat_1(esk14_0))
    | ~ v8_relat_2(esk14_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( esk1_2(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0)) = esk13_0
    | esk13_0 = esk12_0
    | r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0))
    | ~ v8_relat_2(esk14_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_49])).

cnf(c_0_88,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(X1,k1_wellord1(esk14_0,esk12_0))
    | ~ v8_relat_2(esk14_0)
    | ~ r2_hidden(X2,k1_wellord1(esk14_0,esk12_0))
    | ~ r2_hidden(k4_tarski(X1,X2),esk14_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_86]),c_0_19]),c_0_14]),c_0_22])])).

cnf(c_0_89,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))
    | r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0))
    | ~ v8_relat_2(esk14_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_87])).

cnf(c_0_90,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(X1,k1_wellord1(esk14_0,esk12_0))
    | ~ v8_relat_2(esk14_0)
    | ~ r2_hidden(X2,k1_wellord1(esk14_0,esk12_0))
    | ~ r2_hidden(X1,k1_wellord1(esk14_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_35]),c_0_14])])).

cnf(c_0_91,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))
    | ~ v8_relat_2(esk14_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_89]),c_0_29])).

cnf(c_0_92,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(X1,k1_wellord1(esk14_0,esk12_0))
    | ~ v8_relat_2(esk14_0)
    | ~ r2_hidden(X1,k1_wellord1(esk14_0,esk13_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_93,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(esk12_0,k1_wellord1(esk14_0,esk12_0))
    | ~ v8_relat_2(esk14_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_43])).

cnf(c_0_94,negated_conjecture,
    ( esk13_0 = esk12_0
    | ~ v8_relat_2(esk14_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_93]),c_0_14])])).

cnf(c_0_95,negated_conjecture,
    ( esk13_0 = esk12_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_39]),c_0_19]),c_0_14])])).

cnf(c_0_96,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_49])).

fof(c_0_97,plain,(
    ! [X23,X24] :
      ( ( ~ v1_relat_2(X23)
        | ~ r2_hidden(X24,k3_relat_1(X23))
        | r2_hidden(k4_tarski(X24,X24),X23)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(esk3_1(X23),k3_relat_1(X23))
        | v1_relat_2(X23)
        | ~ v1_relat_1(X23) )
      & ( ~ r2_hidden(k4_tarski(esk3_1(X23),esk3_1(X23)),X23)
        | v1_relat_2(X23)
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_wellord1])])])])])).

cnf(c_0_98,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_95]),c_0_95]),c_0_96])])).

cnf(c_0_99,plain,
    ( r2_hidden(k4_tarski(X2,X2),X1)
    | ~ v1_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_100,negated_conjecture,
    ( ~ v1_relat_2(esk14_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_14]),c_0_22])])).

cnf(c_0_101,plain,
    ( v1_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_102,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_19]),c_0_14])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:15:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.54  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.20/0.54  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.54  #
% 0.20/0.54  # Preprocessing time       : 0.030 s
% 0.20/0.54  
% 0.20/0.54  # Proof found!
% 0.20/0.54  # SZS status Theorem
% 0.20/0.54  # SZS output start CNFRefutation
% 0.20/0.54  fof(t37_wellord1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_wellord1)).
% 0.20/0.54  fof(l4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v6_relat_2(X1)<=>![X2, X3]:~(((((r2_hidden(X2,k3_relat_1(X1))&r2_hidden(X3,k3_relat_1(X1)))&X2!=X3)&~(r2_hidden(k4_tarski(X2,X3),X1)))&~(r2_hidden(k4_tarski(X3,X2),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l4_wellord1)).
% 0.20/0.54  fof(d4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)<=>((((v1_relat_2(X1)&v8_relat_2(X1))&v4_relat_2(X1))&v6_relat_2(X1))&v1_wellord1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_wellord1)).
% 0.20/0.54  fof(d1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k1_wellord1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4!=X2&r2_hidden(k4_tarski(X4,X2),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord1)).
% 0.20/0.54  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.54  fof(l2_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v8_relat_2(X1)<=>![X2, X3, X4]:((r2_hidden(k4_tarski(X2,X3),X1)&r2_hidden(k4_tarski(X3,X4),X1))=>r2_hidden(k4_tarski(X2,X4),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l2_wellord1)).
% 0.20/0.54  fof(t30_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k3_relat_1(X3))&r2_hidden(X2,k3_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 0.20/0.54  fof(t36_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>((v2_wellord1(X2)&r1_tarski(X1,k3_relat_1(X2)))=>(~((X1!=k3_relat_1(X2)&![X3]:~((r2_hidden(X3,k3_relat_1(X2))&X1=k1_wellord1(X2,X3)))))<=>![X3]:(r2_hidden(X3,X1)=>![X4]:(r2_hidden(k4_tarski(X4,X3),X2)=>r2_hidden(X4,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_wellord1)).
% 0.20/0.54  fof(l1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v1_relat_2(X1)<=>![X2]:(r2_hidden(X2,k3_relat_1(X1))=>r2_hidden(k4_tarski(X2,X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_wellord1)).
% 0.20/0.54  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2)))))), inference(assume_negation,[status(cth)],[t37_wellord1])).
% 0.20/0.54  fof(c_0_10, plain, ![X33, X34, X35]:((~v6_relat_2(X33)|(~r2_hidden(X34,k3_relat_1(X33))|~r2_hidden(X35,k3_relat_1(X33))|X34=X35|r2_hidden(k4_tarski(X34,X35),X33)|r2_hidden(k4_tarski(X35,X34),X33))|~v1_relat_1(X33))&(((((r2_hidden(esk7_1(X33),k3_relat_1(X33))|v6_relat_2(X33)|~v1_relat_1(X33))&(r2_hidden(esk8_1(X33),k3_relat_1(X33))|v6_relat_2(X33)|~v1_relat_1(X33)))&(esk7_1(X33)!=esk8_1(X33)|v6_relat_2(X33)|~v1_relat_1(X33)))&(~r2_hidden(k4_tarski(esk7_1(X33),esk8_1(X33)),X33)|v6_relat_2(X33)|~v1_relat_1(X33)))&(~r2_hidden(k4_tarski(esk8_1(X33),esk7_1(X33)),X33)|v6_relat_2(X33)|~v1_relat_1(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).
% 0.20/0.54  fof(c_0_11, negated_conjecture, (v1_relat_1(esk14_0)&(((v2_wellord1(esk14_0)&r2_hidden(esk12_0,k3_relat_1(esk14_0)))&r2_hidden(esk13_0,k3_relat_1(esk14_0)))&((~r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)|~r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0)))&(r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)|r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.20/0.54  cnf(c_0_12, plain, (X2=X3|r2_hidden(k4_tarski(X2,X3),X1)|r2_hidden(k4_tarski(X3,X2),X1)|~v6_relat_2(X1)|~r2_hidden(X2,k3_relat_1(X1))|~r2_hidden(X3,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.54  cnf(c_0_13, negated_conjecture, (r2_hidden(esk13_0,k3_relat_1(esk14_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.54  cnf(c_0_14, negated_conjecture, (v1_relat_1(esk14_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.54  fof(c_0_15, plain, ![X22]:((((((v1_relat_2(X22)|~v2_wellord1(X22)|~v1_relat_1(X22))&(v8_relat_2(X22)|~v2_wellord1(X22)|~v1_relat_1(X22)))&(v4_relat_2(X22)|~v2_wellord1(X22)|~v1_relat_1(X22)))&(v6_relat_2(X22)|~v2_wellord1(X22)|~v1_relat_1(X22)))&(v1_wellord1(X22)|~v2_wellord1(X22)|~v1_relat_1(X22)))&(~v1_relat_2(X22)|~v8_relat_2(X22)|~v4_relat_2(X22)|~v6_relat_2(X22)|~v1_wellord1(X22)|v2_wellord1(X22)|~v1_relat_1(X22))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).
% 0.20/0.54  fof(c_0_16, plain, ![X14, X15, X16, X17, X18, X19, X20]:((((X17!=X15|~r2_hidden(X17,X16)|X16!=k1_wellord1(X14,X15)|~v1_relat_1(X14))&(r2_hidden(k4_tarski(X17,X15),X14)|~r2_hidden(X17,X16)|X16!=k1_wellord1(X14,X15)|~v1_relat_1(X14)))&(X18=X15|~r2_hidden(k4_tarski(X18,X15),X14)|r2_hidden(X18,X16)|X16!=k1_wellord1(X14,X15)|~v1_relat_1(X14)))&((~r2_hidden(esk2_3(X14,X19,X20),X20)|(esk2_3(X14,X19,X20)=X19|~r2_hidden(k4_tarski(esk2_3(X14,X19,X20),X19),X14))|X20=k1_wellord1(X14,X19)|~v1_relat_1(X14))&((esk2_3(X14,X19,X20)!=X19|r2_hidden(esk2_3(X14,X19,X20),X20)|X20=k1_wellord1(X14,X19)|~v1_relat_1(X14))&(r2_hidden(k4_tarski(esk2_3(X14,X19,X20),X19),X14)|r2_hidden(esk2_3(X14,X19,X20),X20)|X20=k1_wellord1(X14,X19)|~v1_relat_1(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).
% 0.20/0.54  cnf(c_0_17, negated_conjecture, (X1=esk13_0|r2_hidden(k4_tarski(esk13_0,X1),esk14_0)|r2_hidden(k4_tarski(X1,esk13_0),esk14_0)|~v6_relat_2(esk14_0)|~r2_hidden(X1,k3_relat_1(esk14_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])])).
% 0.20/0.54  cnf(c_0_18, plain, (v6_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.54  cnf(c_0_19, negated_conjecture, (v2_wellord1(esk14_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.54  cnf(c_0_20, plain, (X1=X2|r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_wellord1(X3,X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.54  cnf(c_0_21, negated_conjecture, (X1=esk13_0|r2_hidden(k4_tarski(X1,esk13_0),esk14_0)|r2_hidden(k4_tarski(esk13_0,X1),esk14_0)|~r2_hidden(X1,k3_relat_1(esk14_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_14])])).
% 0.20/0.54  cnf(c_0_22, negated_conjecture, (r2_hidden(esk12_0,k3_relat_1(esk14_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.54  fof(c_0_23, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.54  cnf(c_0_24, plain, (X1=X2|r2_hidden(X1,k1_wellord1(X3,X2))|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X1,X2),X3)), inference(er,[status(thm)],[c_0_20])).
% 0.20/0.54  cnf(c_0_25, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk13_0,esk12_0),esk14_0)|r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.54  fof(c_0_26, plain, ![X26, X27, X28, X29]:((~v8_relat_2(X26)|(~r2_hidden(k4_tarski(X27,X28),X26)|~r2_hidden(k4_tarski(X28,X29),X26)|r2_hidden(k4_tarski(X27,X29),X26))|~v1_relat_1(X26))&(((r2_hidden(k4_tarski(esk4_1(X26),esk5_1(X26)),X26)|v8_relat_2(X26)|~v1_relat_1(X26))&(r2_hidden(k4_tarski(esk5_1(X26),esk6_1(X26)),X26)|v8_relat_2(X26)|~v1_relat_1(X26)))&(~r2_hidden(k4_tarski(esk4_1(X26),esk6_1(X26)),X26)|v8_relat_2(X26)|~v1_relat_1(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l2_wellord1])])])])])).
% 0.20/0.54  cnf(c_0_27, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.54  cnf(c_0_28, negated_conjecture, (r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)|r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.54  cnf(c_0_29, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_14])])).
% 0.20/0.54  cnf(c_0_30, plain, (r2_hidden(k4_tarski(X2,X4),X1)|~v8_relat_2(X1)|~r2_hidden(k4_tarski(X2,X3),X1)|~r2_hidden(k4_tarski(X3,X4),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.54  cnf(c_0_31, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|X4!=k1_wellord1(X3,X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.54  cnf(c_0_32, negated_conjecture, (r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)|r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))|~r2_hidden(X1,k1_wellord1(esk14_0,esk12_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.54  cnf(c_0_33, negated_conjecture, (esk13_0=esk12_0|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))|r2_hidden(esk12_0,k1_wellord1(esk14_0,esk13_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_29]), c_0_14])])).
% 0.20/0.54  cnf(c_0_34, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)|r2_hidden(k4_tarski(X1,esk12_0),esk14_0)|~v8_relat_2(esk14_0)|~r2_hidden(k4_tarski(X1,esk13_0),esk14_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_25]), c_0_14])])).
% 0.20/0.54  cnf(c_0_35, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)|~r2_hidden(X1,k1_wellord1(X3,X2))), inference(er,[status(thm)],[c_0_31])).
% 0.20/0.54  cnf(c_0_36, plain, (X1!=X2|~r2_hidden(X1,X3)|X3!=k1_wellord1(X4,X2)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.54  cnf(c_0_37, negated_conjecture, (esk13_0=esk12_0|r2_hidden(esk12_0,k1_wellord1(esk14_0,esk13_0))|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk13_0))|r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.54  cnf(c_0_38, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)|r2_hidden(k4_tarski(X1,esk12_0),esk14_0)|~v8_relat_2(esk14_0)|~r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_14])])).
% 0.20/0.54  cnf(c_0_39, plain, (v8_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.54  cnf(c_0_40, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k1_wellord1(X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_36])])).
% 0.20/0.54  cnf(c_0_41, negated_conjecture, (esk13_0=esk12_0|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk13_0))|r2_hidden(esk12_0,k1_wellord1(esk14_0,esk13_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_37]), c_0_14])])).
% 0.20/0.54  cnf(c_0_42, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)|r2_hidden(k4_tarski(X1,esk12_0),esk14_0)|~r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_19]), c_0_14])])).
% 0.20/0.54  cnf(c_0_43, negated_conjecture, (esk13_0=esk12_0|r2_hidden(esk12_0,k1_wellord1(esk14_0,esk13_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_14])])).
% 0.20/0.54  cnf(c_0_44, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)|r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.54  cnf(c_0_45, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)|r2_hidden(k4_tarski(X1,esk13_0),esk14_0)|~v8_relat_2(esk14_0)|~r2_hidden(k4_tarski(X1,esk12_0),esk14_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_44]), c_0_14])])).
% 0.20/0.54  cnf(c_0_46, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)|r2_hidden(k4_tarski(X1,esk13_0),esk14_0)|~r2_hidden(k4_tarski(X1,esk12_0),esk14_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_39]), c_0_19]), c_0_14])])).
% 0.20/0.54  fof(c_0_47, plain, ![X11, X12, X13]:((r2_hidden(X11,k3_relat_1(X13))|~r2_hidden(k4_tarski(X11,X12),X13)|~v1_relat_1(X13))&(r2_hidden(X12,k3_relat_1(X13))|~r2_hidden(k4_tarski(X11,X12),X13)|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).
% 0.20/0.54  cnf(c_0_48, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)|r2_hidden(k4_tarski(X1,esk13_0),esk14_0)|~r2_hidden(X1,k1_wellord1(esk14_0,esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_35]), c_0_14])])).
% 0.20/0.54  cnf(c_0_49, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.54  fof(c_0_50, plain, ![X38, X39, X40, X41, X42]:(((X38!=k3_relat_1(X39)|(~r2_hidden(X41,X38)|(~r2_hidden(k4_tarski(X42,X41),X39)|r2_hidden(X42,X38)))|(~v2_wellord1(X39)|~r1_tarski(X38,k3_relat_1(X39)))|~v1_relat_1(X39))&(~r2_hidden(X40,k3_relat_1(X39))|X38!=k1_wellord1(X39,X40)|(~r2_hidden(X41,X38)|(~r2_hidden(k4_tarski(X42,X41),X39)|r2_hidden(X42,X38)))|(~v2_wellord1(X39)|~r1_tarski(X38,k3_relat_1(X39)))|~v1_relat_1(X39)))&(((r2_hidden(esk11_2(X38,X39),k3_relat_1(X39))|X38=k3_relat_1(X39)|r2_hidden(esk9_2(X38,X39),X38)|(~v2_wellord1(X39)|~r1_tarski(X38,k3_relat_1(X39)))|~v1_relat_1(X39))&(X38=k1_wellord1(X39,esk11_2(X38,X39))|X38=k3_relat_1(X39)|r2_hidden(esk9_2(X38,X39),X38)|(~v2_wellord1(X39)|~r1_tarski(X38,k3_relat_1(X39)))|~v1_relat_1(X39)))&(((r2_hidden(esk11_2(X38,X39),k3_relat_1(X39))|X38=k3_relat_1(X39)|r2_hidden(k4_tarski(esk10_2(X38,X39),esk9_2(X38,X39)),X39)|(~v2_wellord1(X39)|~r1_tarski(X38,k3_relat_1(X39)))|~v1_relat_1(X39))&(X38=k1_wellord1(X39,esk11_2(X38,X39))|X38=k3_relat_1(X39)|r2_hidden(k4_tarski(esk10_2(X38,X39),esk9_2(X38,X39)),X39)|(~v2_wellord1(X39)|~r1_tarski(X38,k3_relat_1(X39)))|~v1_relat_1(X39)))&((r2_hidden(esk11_2(X38,X39),k3_relat_1(X39))|X38=k3_relat_1(X39)|~r2_hidden(esk10_2(X38,X39),X38)|(~v2_wellord1(X39)|~r1_tarski(X38,k3_relat_1(X39)))|~v1_relat_1(X39))&(X38=k1_wellord1(X39,esk11_2(X38,X39))|X38=k3_relat_1(X39)|~r2_hidden(esk10_2(X38,X39),X38)|(~v2_wellord1(X39)|~r1_tarski(X38,k3_relat_1(X39)))|~v1_relat_1(X39)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_wellord1])])])])])).
% 0.20/0.54  cnf(c_0_51, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.54  cnf(c_0_52, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk1_2(k1_wellord1(esk14_0,esk12_0),X1),esk13_0),esk14_0)|r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)|r1_tarski(k1_wellord1(esk14_0,esk12_0),X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.54  cnf(c_0_53, plain, (r2_hidden(X5,X3)|~r2_hidden(X1,k3_relat_1(X2))|X3!=k1_wellord1(X2,X1)|~r2_hidden(X4,X3)|~r2_hidden(k4_tarski(X5,X4),X2)|~v2_wellord1(X2)|~r1_tarski(X3,k3_relat_1(X2))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.54  cnf(c_0_54, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.54  cnf(c_0_55, negated_conjecture, (esk13_0=esk12_0|r2_hidden(esk1_2(k1_wellord1(esk14_0,esk12_0),X1),k3_relat_1(esk14_0))|r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)|r1_tarski(k1_wellord1(esk14_0,esk12_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_14])])).
% 0.20/0.54  cnf(c_0_56, plain, (r2_hidden(X1,k1_wellord1(X2,X3))|~v2_wellord1(X2)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,k1_wellord1(X2,X3))|~r2_hidden(X3,k3_relat_1(X2))|~r1_tarski(k1_wellord1(X2,X3),k3_relat_1(X2))), inference(er,[status(thm)],[c_0_53])).
% 0.20/0.54  cnf(c_0_57, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)|r1_tarski(k1_wellord1(esk14_0,esk12_0),k3_relat_1(esk14_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.54  cnf(c_0_58, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)|r2_hidden(X1,k1_wellord1(esk14_0,esk12_0))|~r2_hidden(X2,k1_wellord1(esk14_0,esk12_0))|~r2_hidden(k4_tarski(X1,X2),esk14_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_19]), c_0_14]), c_0_22])])).
% 0.20/0.54  cnf(c_0_59, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)|r2_hidden(X1,k1_wellord1(esk14_0,esk12_0))|~r2_hidden(X2,k1_wellord1(esk14_0,esk12_0))|~r2_hidden(X1,k1_wellord1(esk14_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_35]), c_0_14])])).
% 0.20/0.54  cnf(c_0_60, negated_conjecture, (esk1_2(k1_wellord1(esk14_0,esk12_0),X1)=esk13_0|esk13_0=esk12_0|r2_hidden(esk1_2(k1_wellord1(esk14_0,esk12_0),X1),k1_wellord1(esk14_0,esk13_0))|r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)|r1_tarski(k1_wellord1(esk14_0,esk12_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_52]), c_0_14])])).
% 0.20/0.54  cnf(c_0_61, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)|r2_hidden(X1,k1_wellord1(esk14_0,esk12_0))|r1_tarski(k1_wellord1(esk14_0,esk12_0),X2)|~r2_hidden(X1,k1_wellord1(esk14_0,esk1_2(k1_wellord1(esk14_0,esk12_0),X2)))), inference(spm,[status(thm)],[c_0_59, c_0_49])).
% 0.20/0.54  cnf(c_0_62, negated_conjecture, (esk1_2(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0))=esk13_0|esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)|r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0))), inference(spm,[status(thm)],[c_0_54, c_0_60])).
% 0.20/0.54  cnf(c_0_63, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)|r2_hidden(X1,k1_wellord1(esk14_0,esk12_0))|r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0))|~r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.54  cnf(c_0_64, plain, (r2_hidden(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(X1,k1_wellord1(X2,X3))), inference(spm,[status(thm)],[c_0_51, c_0_35])).
% 0.20/0.54  cnf(c_0_65, negated_conjecture, (esk13_0=esk12_0|r2_hidden(esk1_2(k1_wellord1(esk14_0,esk13_0),X1),k1_wellord1(esk14_0,esk12_0))|r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)|r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0))|r1_tarski(k1_wellord1(esk14_0,esk13_0),X1)), inference(spm,[status(thm)],[c_0_63, c_0_49])).
% 0.20/0.54  cnf(c_0_66, negated_conjecture, (esk13_0=esk12_0|r2_hidden(esk1_2(k1_wellord1(esk14_0,esk13_0),X1),k3_relat_1(esk14_0))|r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)|r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0))|r1_tarski(k1_wellord1(esk14_0,esk13_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_14])])).
% 0.20/0.54  cnf(c_0_67, negated_conjecture, (~r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)|~r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.54  cnf(c_0_68, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)|r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0))|r1_tarski(k1_wellord1(esk14_0,esk13_0),k3_relat_1(esk14_0))), inference(spm,[status(thm)],[c_0_54, c_0_66])).
% 0.20/0.54  cnf(c_0_69, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)|r1_tarski(k1_wellord1(esk14_0,esk13_0),k3_relat_1(esk14_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_44])).
% 0.20/0.54  cnf(c_0_70, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)|r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))|~r2_hidden(X2,k1_wellord1(esk14_0,esk13_0))|~r2_hidden(k4_tarski(X1,X2),esk14_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_69]), c_0_19]), c_0_14]), c_0_13])])).
% 0.20/0.54  cnf(c_0_71, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)|r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))|~r2_hidden(X2,k1_wellord1(esk14_0,esk13_0))|~r2_hidden(X1,k1_wellord1(esk14_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_35]), c_0_14])])).
% 0.20/0.54  cnf(c_0_72, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)|r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))|~r2_hidden(X1,k1_wellord1(esk14_0,esk12_0))), inference(spm,[status(thm)],[c_0_71, c_0_43])).
% 0.20/0.54  cnf(c_0_73, negated_conjecture, (esk13_0=esk12_0|r2_hidden(esk1_2(k1_wellord1(esk14_0,esk12_0),X1),k1_wellord1(esk14_0,esk13_0))|r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)|r1_tarski(k1_wellord1(esk14_0,esk12_0),X1)), inference(spm,[status(thm)],[c_0_72, c_0_49])).
% 0.20/0.54  cnf(c_0_74, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)|r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0))), inference(spm,[status(thm)],[c_0_54, c_0_73])).
% 0.20/0.54  cnf(c_0_75, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~v8_relat_2(X3)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X1,X4),X3)|~r2_hidden(X4,k1_wellord1(X3,X2))), inference(spm,[status(thm)],[c_0_30, c_0_35])).
% 0.20/0.54  cnf(c_0_76, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_74]), c_0_44])).
% 0.20/0.54  cnf(c_0_77, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,X1),esk14_0)|~v8_relat_2(esk14_0)|~r2_hidden(esk12_0,k1_wellord1(esk14_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_14])])).
% 0.20/0.54  cnf(c_0_78, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(X1,X2),esk14_0)|~v8_relat_2(esk14_0)|~r2_hidden(k4_tarski(X1,esk12_0),esk14_0)|~r2_hidden(esk12_0,k1_wellord1(esk14_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_77]), c_0_14])])).
% 0.20/0.54  cnf(c_0_79, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(X1,X2),esk14_0)|~v8_relat_2(esk14_0)|~r2_hidden(esk12_0,k1_wellord1(esk14_0,X2))|~r2_hidden(X1,k1_wellord1(esk14_0,esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_35]), c_0_14])])).
% 0.20/0.54  cnf(c_0_80, negated_conjecture, (esk13_0=esk12_0|r2_hidden(X1,k3_relat_1(esk14_0))|~v8_relat_2(esk14_0)|~r2_hidden(esk12_0,k1_wellord1(esk14_0,X2))|~r2_hidden(X1,k1_wellord1(esk14_0,esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_79]), c_0_14])])).
% 0.20/0.54  cnf(c_0_81, negated_conjecture, (esk13_0=esk12_0|X1=X2|r2_hidden(X1,k1_wellord1(esk14_0,X2))|~v8_relat_2(esk14_0)|~r2_hidden(esk12_0,k1_wellord1(esk14_0,X2))|~r2_hidden(X1,k1_wellord1(esk14_0,esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_79]), c_0_14])])).
% 0.20/0.54  cnf(c_0_82, negated_conjecture, (esk13_0=esk12_0|r2_hidden(X1,k3_relat_1(esk14_0))|~v8_relat_2(esk14_0)|~r2_hidden(X1,k1_wellord1(esk14_0,esk12_0))), inference(spm,[status(thm)],[c_0_80, c_0_43])).
% 0.20/0.54  cnf(c_0_83, negated_conjecture, (esk13_0=esk12_0|X1=esk13_0|r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))|~v8_relat_2(esk14_0)|~r2_hidden(X1,k1_wellord1(esk14_0,esk12_0))), inference(spm,[status(thm)],[c_0_81, c_0_43])).
% 0.20/0.54  cnf(c_0_84, negated_conjecture, (esk13_0=esk12_0|r2_hidden(esk1_2(k1_wellord1(esk14_0,esk12_0),X1),k3_relat_1(esk14_0))|r1_tarski(k1_wellord1(esk14_0,esk12_0),X1)|~v8_relat_2(esk14_0)), inference(spm,[status(thm)],[c_0_82, c_0_49])).
% 0.20/0.54  cnf(c_0_85, negated_conjecture, (esk1_2(X1,k1_wellord1(esk14_0,esk13_0))=esk13_0|esk13_0=esk12_0|r1_tarski(X1,k1_wellord1(esk14_0,esk13_0))|~v8_relat_2(esk14_0)|~r2_hidden(esk1_2(X1,k1_wellord1(esk14_0,esk13_0)),k1_wellord1(esk14_0,esk12_0))), inference(spm,[status(thm)],[c_0_54, c_0_83])).
% 0.20/0.54  cnf(c_0_86, negated_conjecture, (esk13_0=esk12_0|r1_tarski(k1_wellord1(esk14_0,esk12_0),k3_relat_1(esk14_0))|~v8_relat_2(esk14_0)), inference(spm,[status(thm)],[c_0_54, c_0_84])).
% 0.20/0.54  cnf(c_0_87, negated_conjecture, (esk1_2(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0))=esk13_0|esk13_0=esk12_0|r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0))|~v8_relat_2(esk14_0)), inference(spm,[status(thm)],[c_0_85, c_0_49])).
% 0.20/0.54  cnf(c_0_88, negated_conjecture, (esk13_0=esk12_0|r2_hidden(X1,k1_wellord1(esk14_0,esk12_0))|~v8_relat_2(esk14_0)|~r2_hidden(X2,k1_wellord1(esk14_0,esk12_0))|~r2_hidden(k4_tarski(X1,X2),esk14_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_86]), c_0_19]), c_0_14]), c_0_22])])).
% 0.20/0.54  cnf(c_0_89, negated_conjecture, (esk13_0=esk12_0|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))|r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0))|~v8_relat_2(esk14_0)), inference(spm,[status(thm)],[c_0_49, c_0_87])).
% 0.20/0.54  cnf(c_0_90, negated_conjecture, (esk13_0=esk12_0|r2_hidden(X1,k1_wellord1(esk14_0,esk12_0))|~v8_relat_2(esk14_0)|~r2_hidden(X2,k1_wellord1(esk14_0,esk12_0))|~r2_hidden(X1,k1_wellord1(esk14_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_35]), c_0_14])])).
% 0.20/0.54  cnf(c_0_91, negated_conjecture, (esk13_0=esk12_0|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))|~v8_relat_2(esk14_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_89]), c_0_29])).
% 0.20/0.54  cnf(c_0_92, negated_conjecture, (esk13_0=esk12_0|r2_hidden(X1,k1_wellord1(esk14_0,esk12_0))|~v8_relat_2(esk14_0)|~r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.20/0.54  cnf(c_0_93, negated_conjecture, (esk13_0=esk12_0|r2_hidden(esk12_0,k1_wellord1(esk14_0,esk12_0))|~v8_relat_2(esk14_0)), inference(spm,[status(thm)],[c_0_92, c_0_43])).
% 0.20/0.54  cnf(c_0_94, negated_conjecture, (esk13_0=esk12_0|~v8_relat_2(esk14_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_93]), c_0_14])])).
% 0.20/0.54  cnf(c_0_95, negated_conjecture, (esk13_0=esk12_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_39]), c_0_19]), c_0_14])])).
% 0.20/0.54  cnf(c_0_96, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_54, c_0_49])).
% 0.20/0.54  fof(c_0_97, plain, ![X23, X24]:((~v1_relat_2(X23)|(~r2_hidden(X24,k3_relat_1(X23))|r2_hidden(k4_tarski(X24,X24),X23))|~v1_relat_1(X23))&((r2_hidden(esk3_1(X23),k3_relat_1(X23))|v1_relat_2(X23)|~v1_relat_1(X23))&(~r2_hidden(k4_tarski(esk3_1(X23),esk3_1(X23)),X23)|v1_relat_2(X23)|~v1_relat_1(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_wellord1])])])])])).
% 0.20/0.54  cnf(c_0_98, negated_conjecture, (~r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_95]), c_0_95]), c_0_96])])).
% 0.20/0.54  cnf(c_0_99, plain, (r2_hidden(k4_tarski(X2,X2),X1)|~v1_relat_2(X1)|~r2_hidden(X2,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.20/0.54  cnf(c_0_100, negated_conjecture, (~v1_relat_2(esk14_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_14]), c_0_22])])).
% 0.20/0.54  cnf(c_0_101, plain, (v1_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.54  cnf(c_0_102, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_19]), c_0_14])]), ['proof']).
% 0.20/0.54  # SZS output end CNFRefutation
% 0.20/0.54  # Proof object total steps             : 103
% 0.20/0.54  # Proof object clause steps            : 84
% 0.20/0.54  # Proof object formula steps           : 19
% 0.20/0.54  # Proof object conjectures             : 66
% 0.20/0.54  # Proof object clause conjectures      : 63
% 0.20/0.54  # Proof object formula conjectures     : 3
% 0.20/0.54  # Proof object initial clauses used    : 20
% 0.20/0.54  # Proof object initial formulas used   : 9
% 0.20/0.54  # Proof object generating inferences   : 59
% 0.20/0.54  # Proof object simplifying inferences  : 84
% 0.20/0.54  # Training examples: 0 positive, 0 negative
% 0.20/0.54  # Parsed axioms                        : 9
% 0.20/0.54  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.54  # Initial clauses                      : 44
% 0.20/0.54  # Removed in clause preprocessing      : 0
% 0.20/0.54  # Initial clauses in saturation        : 44
% 0.20/0.54  # Processed clauses                    : 675
% 0.20/0.54  # ...of these trivial                  : 0
% 0.20/0.54  # ...subsumed                          : 199
% 0.20/0.54  # ...remaining for further processing  : 476
% 0.20/0.54  # Other redundant clauses eliminated   : 6
% 0.20/0.54  # Clauses deleted for lack of memory   : 0
% 0.20/0.54  # Backward-subsumed                    : 173
% 0.20/0.54  # Backward-rewritten                   : 94
% 0.20/0.54  # Generated clauses                    : 2760
% 0.20/0.54  # ...of the previous two non-trivial   : 2323
% 0.20/0.54  # Contextual simplify-reflections      : 10
% 0.20/0.54  # Paramodulations                      : 2752
% 0.20/0.54  # Factorizations                       : 0
% 0.20/0.54  # Equation resolutions                 : 6
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
% 0.20/0.54  # Current number of processed clauses  : 201
% 0.20/0.54  #    Positive orientable unit clauses  : 5
% 0.20/0.54  #    Positive unorientable unit clauses: 0
% 0.20/0.54  #    Negative unit clauses             : 3
% 0.20/0.54  #    Non-unit-clauses                  : 193
% 0.20/0.54  # Current number of unprocessed clauses: 1252
% 0.20/0.54  # ...number of literals in the above   : 9591
% 0.20/0.54  # Current number of archived formulas  : 0
% 0.20/0.54  # Current number of archived clauses   : 270
% 0.20/0.54  # Clause-clause subsumption calls (NU) : 48367
% 0.20/0.54  # Rec. Clause-clause subsumption calls : 1703
% 0.20/0.54  # Non-unit clause-clause subsumptions  : 382
% 0.20/0.54  # Unit Clause-clause subsumption calls : 41
% 0.20/0.54  # Rewrite failures with RHS unbound    : 0
% 0.20/0.54  # BW rewrite match attempts            : 6
% 0.20/0.54  # BW rewrite match successes           : 1
% 0.20/0.54  # Condensation attempts                : 0
% 0.20/0.54  # Condensation successes               : 0
% 0.20/0.54  # Termbank termtop insertions          : 141631
% 0.20/0.54  
% 0.20/0.54  # -------------------------------------------------
% 0.20/0.54  # User time                : 0.183 s
% 0.20/0.54  # System time              : 0.011 s
% 0.20/0.54  # Total time               : 0.195 s
% 0.20/0.54  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
