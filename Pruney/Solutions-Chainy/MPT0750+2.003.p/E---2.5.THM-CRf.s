%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:32 EST 2020

% Result     : Theorem 10.07s
% Output     : CNFRefutation 10.07s
% Verified   : 
% Statistics : Number of formulae       :  217 (101416 expanded)
%              Number of clauses        :  180 (45760 expanded)
%              Number of leaves         :   18 (23952 expanded)
%              Depth                    :   42
%              Number of atoms          :  576 (400895 expanded)
%              Number of equality atoms :   46 (32419 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v4_ordinal1(X1)
      <=> ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X2,X1)
             => r2_hidden(k1_ordinal1(X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(t35_ordinal1,axiom,(
    ! [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
         => v3_ordinal1(X2) )
     => v3_ordinal1(k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_ordinal1)).

fof(d6_ordinal1,axiom,(
    ! [X1] :
      ( v4_ordinal1(X1)
    <=> X1 = k3_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_ordinal1)).

fof(t23_ordinal1,axiom,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ( r2_hidden(X1,X2)
       => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

fof(t29_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k1_ordinal1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(t39_ordinal1,axiom,(
    ! [X1] :
    ? [X2] :
      ( v3_ordinal1(X2)
      & ~ r2_hidden(X2,X1)
      & ! [X3] :
          ( v3_ordinal1(X3)
         => ( ~ r2_hidden(X3,X1)
           => r1_ordinal1(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_ordinal1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(t13_ordinal1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,k1_ordinal1(X2))
    <=> ( r2_hidden(X1,X2)
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(t34_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,k1_ordinal1(X2))
          <=> r1_ordinal1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(d2_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ( v4_ordinal1(X1)
        <=> ! [X2] :
              ( v3_ordinal1(X2)
             => ( r2_hidden(X2,X1)
               => r2_hidden(k1_ordinal1(X2),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t41_ordinal1])).

fof(c_0_19,plain,(
    ! [X40,X41] :
      ( ~ v3_ordinal1(X40)
      | ~ v3_ordinal1(X41)
      | r2_hidden(X40,X41)
      | X40 = X41
      | r2_hidden(X41,X40) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

fof(c_0_20,negated_conjecture,(
    ! [X54] :
      ( v3_ordinal1(esk8_0)
      & ( v3_ordinal1(esk9_0)
        | ~ v4_ordinal1(esk8_0) )
      & ( r2_hidden(esk9_0,esk8_0)
        | ~ v4_ordinal1(esk8_0) )
      & ( ~ r2_hidden(k1_ordinal1(esk9_0),esk8_0)
        | ~ v4_ordinal1(esk8_0) )
      & ( v4_ordinal1(esk8_0)
        | ~ v3_ordinal1(X54)
        | ~ r2_hidden(X54,esk8_0)
        | r2_hidden(k1_ordinal1(X54),esk8_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])])])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( v3_ordinal1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_23,plain,(
    ! [X45] :
      ( ( r2_hidden(esk6_1(X45),X45)
        | v3_ordinal1(k3_tarski(X45)) )
      & ( ~ v3_ordinal1(esk6_1(X45))
        | v3_ordinal1(k3_tarski(X45)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_ordinal1])])])])).

fof(c_0_24,plain,(
    ! [X32] :
      ( ( ~ v4_ordinal1(X32)
        | X32 = k3_tarski(X32) )
      & ( X32 != k3_tarski(X32)
        | v4_ordinal1(X32) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_ordinal1])])).

cnf(c_0_25,negated_conjecture,
    ( X1 = esk8_0
    | r2_hidden(X1,esk8_0)
    | r2_hidden(esk8_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( r2_hidden(esk6_1(X1),X1)
    | v3_ordinal1(k3_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X38,X39] :
      ( ~ v3_ordinal1(X39)
      | ~ r2_hidden(X38,X39)
      | v3_ordinal1(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

cnf(c_0_28,plain,
    ( v4_ordinal1(X1)
    | X1 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( k3_tarski(X1) = esk8_0
    | r2_hidden(esk8_0,k3_tarski(X1))
    | r2_hidden(k3_tarski(X1),esk8_0)
    | r2_hidden(esk6_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk9_0,esk8_0)
    | ~ v4_ordinal1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( v4_ordinal1(esk8_0)
    | r2_hidden(esk6_1(esk8_0),esk8_0)
    | r2_hidden(k3_tarski(esk8_0),esk8_0)
    | r2_hidden(esk8_0,k3_tarski(esk8_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29])])).

cnf(c_0_33,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk8_0,k3_tarski(esk8_0))
    | r2_hidden(k3_tarski(esk8_0),esk8_0)
    | r2_hidden(esk6_1(esk8_0),esk8_0)
    | r2_hidden(esk9_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,plain,
    ( v3_ordinal1(k3_tarski(X1))
    | ~ v3_ordinal1(esk6_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( v3_ordinal1(esk6_1(esk8_0))
    | r2_hidden(k3_tarski(esk8_0),esk8_0)
    | r2_hidden(esk8_0,k3_tarski(esk8_0))
    | r2_hidden(esk9_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_37,plain,(
    ! [X42] :
      ( ~ v3_ordinal1(X42)
      | v3_ordinal1(k1_ordinal1(X42)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

fof(c_0_38,plain,(
    ! [X27] : k1_ordinal1(X27) = k2_xboole_0(X27,k1_tarski(X27)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_39,plain,(
    ! [X50,X51] :
      ( ~ r2_hidden(X50,X51)
      | ~ r1_tarski(X51,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_40,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_41,negated_conjecture,
    ( v3_ordinal1(k3_tarski(esk8_0))
    | r2_hidden(esk8_0,k3_tarski(esk8_0))
    | r2_hidden(esk9_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_33])).

cnf(c_0_42,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_44,plain,(
    ! [X35] : r2_hidden(X35,k1_ordinal1(X35)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

fof(c_0_45,plain,(
    ! [X47,X49] :
      ( v3_ordinal1(esk7_1(X47))
      & ~ r2_hidden(esk7_1(X47),X47)
      & ( ~ v3_ordinal1(X49)
        | r2_hidden(X49,X47)
        | r1_ordinal1(esk7_1(X47),X49) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_ordinal1])])])])])).

cnf(c_0_46,negated_conjecture,
    ( v4_ordinal1(esk8_0)
    | r2_hidden(k1_ordinal1(X1),esk8_0)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( k3_tarski(esk8_0) = esk8_0
    | r2_hidden(esk8_0,k3_tarski(esk8_0))
    | r2_hidden(k3_tarski(esk8_0),esk8_0)
    | r2_hidden(esk9_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_41])).

cnf(c_0_50,plain,
    ( v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( v3_ordinal1(esk7_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_53,plain,(
    ! [X13,X14,X15,X17,X18,X19,X20,X22] :
      ( ( r2_hidden(X15,esk2_3(X13,X14,X15))
        | ~ r2_hidden(X15,X14)
        | X14 != k3_tarski(X13) )
      & ( r2_hidden(esk2_3(X13,X14,X15),X13)
        | ~ r2_hidden(X15,X14)
        | X14 != k3_tarski(X13) )
      & ( ~ r2_hidden(X17,X18)
        | ~ r2_hidden(X18,X13)
        | r2_hidden(X17,X14)
        | X14 != k3_tarski(X13) )
      & ( ~ r2_hidden(esk3_2(X19,X20),X20)
        | ~ r2_hidden(esk3_2(X19,X20),X22)
        | ~ r2_hidden(X22,X19)
        | X20 = k3_tarski(X19) )
      & ( r2_hidden(esk3_2(X19,X20),esk4_2(X19,X20))
        | r2_hidden(esk3_2(X19,X20),X20)
        | X20 = k3_tarski(X19) )
      & ( r2_hidden(esk4_2(X19,X20),X19)
        | r2_hidden(esk3_2(X19,X20),X20)
        | X20 = k3_tarski(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_54,negated_conjecture,
    ( v4_ordinal1(esk8_0)
    | r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk8_0)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(rw,[status(thm)],[c_0_46,c_0_43])).

cnf(c_0_55,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(k3_tarski(esk8_0),esk8_0)
    | r2_hidden(esk8_0,k3_tarski(esk8_0))
    | r2_hidden(esk9_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_49]),c_0_31])).

cnf(c_0_57,negated_conjecture,
    ( v3_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_22])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_51,c_0_43])).

fof(c_0_59,plain,(
    ! [X24] :
      ( ( v1_ordinal1(X24)
        | ~ v3_ordinal1(X24) )
      & ( v2_ordinal1(X24)
        | ~ v3_ordinal1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

fof(c_0_60,plain,(
    ! [X36,X37] :
      ( ( ~ r2_hidden(X36,k1_ordinal1(X37))
        | r2_hidden(X36,X37)
        | X36 = X37 )
      & ( ~ r2_hidden(X36,X37)
        | r2_hidden(X36,k1_ordinal1(X37)) )
      & ( X36 != X37
        | r2_hidden(X36,k1_ordinal1(X37)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(esk7_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_62,negated_conjecture,
    ( esk7_1(X1) = esk8_0
    | r2_hidden(esk8_0,esk7_1(X1))
    | r2_hidden(esk7_1(X1),esk8_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_52])).

fof(c_0_63,plain,(
    ! [X43,X44] :
      ( ( ~ r2_hidden(X43,k1_ordinal1(X44))
        | r1_ordinal1(X43,X44)
        | ~ v3_ordinal1(X44)
        | ~ v3_ordinal1(X43) )
      & ( ~ r1_ordinal1(X43,X44)
        | r2_hidden(X43,k1_ordinal1(X44))
        | ~ v3_ordinal1(X44)
        | ~ v3_ordinal1(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_65,negated_conjecture,
    ( v4_ordinal1(esk8_0)
    | r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk8_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(csr,[status(thm)],[c_0_54,c_0_33])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk1_2(esk8_0,k3_tarski(esk8_0)),esk8_0)
    | r2_hidden(esk8_0,k3_tarski(esk8_0))
    | r2_hidden(esk9_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

fof(c_0_67,plain,(
    ! [X33,X34] :
      ( ( ~ r1_ordinal1(X33,X34)
        | r1_tarski(X33,X34)
        | ~ v3_ordinal1(X33)
        | ~ v3_ordinal1(X34) )
      & ( ~ r1_tarski(X33,X34)
        | r1_ordinal1(X33,X34)
        | ~ v3_ordinal1(X33)
        | ~ v3_ordinal1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_68,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_57])).

cnf(c_0_69,plain,
    ( r2_hidden(esk1_2(k2_xboole_0(X1,k1_tarski(X1)),X1),k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_58])).

fof(c_0_70,plain,(
    ! [X28,X29,X30] :
      ( ( ~ v1_ordinal1(X28)
        | ~ r2_hidden(X29,X28)
        | r1_tarski(X29,X28) )
      & ( r2_hidden(esk5_1(X30),X30)
        | v1_ordinal1(X30) )
      & ( ~ r1_tarski(esk5_1(X30),X30)
        | v1_ordinal1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

cnf(c_0_71,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk7_1(X1),esk8_0)
    | r2_hidden(esk8_0,esk7_1(X1))
    | ~ r2_hidden(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_74,plain,
    ( r1_ordinal1(X1,X2)
    | ~ r2_hidden(X1,k1_ordinal1(X2))
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_64])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk1_2(esk8_0,k3_tarski(esk8_0)),k1_tarski(esk1_2(esk8_0,k3_tarski(esk8_0)))),esk8_0)
    | r2_hidden(esk8_0,k3_tarski(esk8_0))
    | r2_hidden(esk9_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_31])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_78,negated_conjecture,
    ( v3_ordinal1(esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_79,plain,
    ( r1_tarski(X2,X1)
    | ~ v1_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_80,plain,
    ( v1_ordinal1(esk7_1(X1)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_52])).

cnf(c_0_81,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_72,c_0_43])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_1(k2_xboole_0(esk8_0,k1_tarski(esk8_0))))
    | r2_hidden(esk7_1(k2_xboole_0(esk8_0,k1_tarski(esk8_0))),esk8_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_58])).

cnf(c_0_83,plain,
    ( r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_74,c_0_43])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk8_0,k3_tarski(esk8_0))
    | r2_hidden(X1,k3_tarski(esk8_0))
    | r2_hidden(esk9_0,esk8_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk1_2(esk8_0,k3_tarski(esk8_0)),k1_tarski(esk1_2(esk8_0,k3_tarski(esk8_0))))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(X1,esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0))
    | ~ r1_ordinal1(X1,esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_86,plain,
    ( r2_hidden(X1,X2)
    | r1_ordinal1(esk7_1(X2),X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,esk7_1(X2))
    | ~ r2_hidden(X1,esk7_1(X2)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_61])).

cnf(c_0_89,negated_conjecture,
    ( r1_ordinal1(X1,esk8_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_22]),c_0_68])).

cnf(c_0_90,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(esk1_2(esk8_0,k3_tarski(esk8_0)),k3_tarski(esk8_0))
    | r2_hidden(esk8_0,k3_tarski(esk8_0))
    | r2_hidden(esk9_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_58])).

cnf(c_0_92,plain,
    ( r1_tarski(X1,esk7_1(X2))
    | ~ r1_ordinal1(X1,esk7_1(X2))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_52])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(esk7_1(X1),esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0))
    | ~ r1_ordinal1(esk7_1(X1),esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_52])).

cnf(c_0_94,negated_conjecture,
    ( r1_ordinal1(esk7_1(X1),esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0))
    | r2_hidden(esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0),X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_78])).

cnf(c_0_95,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(esk8_0,esk7_1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(X1,esk8_0)
    | ~ r1_ordinal1(X1,esk8_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_22])).

cnf(c_0_98,negated_conjecture,
    ( r1_ordinal1(esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_69])).

fof(c_0_99,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_100,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_101,negated_conjecture,
    ( r2_hidden(esk8_0,k3_tarski(esk8_0))
    | r2_hidden(esk9_0,esk8_0)
    | r1_tarski(esk8_0,k3_tarski(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_102,plain,
    ( r1_tarski(esk7_1(X1),esk7_1(X2))
    | ~ r1_ordinal1(esk7_1(X1),esk7_1(X2)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_52])).

cnf(c_0_103,plain,
    ( r1_ordinal1(esk7_1(X1),esk7_1(X2))
    | r2_hidden(esk7_1(X2),X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_52])).

cnf(c_0_104,negated_conjecture,
    ( r2_hidden(esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0),X1)
    | r1_tarski(esk7_1(X1),esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_105,negated_conjecture,
    ( r2_hidden(X1,esk7_1(k2_xboole_0(esk8_0,k1_tarski(esk8_0))))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_106,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_1(esk7_1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)))))
    | r2_hidden(esk7_1(esk7_1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)))),esk8_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_88])).

cnf(c_0_107,negated_conjecture,
    ( r1_tarski(esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_78]),c_0_98])])).

cnf(c_0_108,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_109,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_110,negated_conjecture,
    ( v1_ordinal1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_22])).

cnf(c_0_111,plain,
    ( r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_100])).

cnf(c_0_112,negated_conjecture,
    ( r2_hidden(esk8_0,k3_tarski(esk8_0))
    | r2_hidden(esk9_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_101]),c_0_56])).

cnf(c_0_113,plain,
    ( r2_hidden(X1,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k3_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_114,plain,
    ( r2_hidden(esk7_1(X1),X2)
    | r1_tarski(esk7_1(X2),esk7_1(X1)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_115,negated_conjecture,
    ( r2_hidden(esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0),X1)
    | r2_hidden(X2,esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0))
    | ~ r2_hidden(X2,esk7_1(X1)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_104])).

cnf(c_0_116,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_1(esk7_1(k2_xboole_0(esk8_0,k1_tarski(esk8_0))))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_61])).

cnf(c_0_117,negated_conjecture,
    ( ~ r2_hidden(esk8_0,esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_107])).

cnf(c_0_118,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r1_ordinal1(X1,X2) ),
    inference(rw,[status(thm)],[c_0_108,c_0_43])).

cnf(c_0_119,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_109])).

cnf(c_0_120,negated_conjecture,
    ( r1_tarski(X1,esk8_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_110])).

cnf(c_0_121,negated_conjecture,
    ( r2_hidden(esk2_3(esk8_0,k3_tarski(esk8_0),esk8_0),esk8_0)
    | r2_hidden(esk9_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_111,c_0_112])).

cnf(c_0_122,plain,
    ( r2_hidden(X1,esk2_3(X2,k3_tarski(X2),X1))
    | ~ r2_hidden(X1,k3_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_113])).

cnf(c_0_123,plain,
    ( r2_hidden(esk7_1(X1),X2)
    | r2_hidden(X3,esk7_1(X1))
    | ~ r2_hidden(X3,esk7_1(X2)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_114])).

cnf(c_0_124,negated_conjecture,
    ( r2_hidden(esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0),esk7_1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_117])).

cnf(c_0_125,plain,
    ( r1_ordinal1(X1,X2)
    | ~ r1_tarski(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_126,negated_conjecture,
    ( r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | ~ r1_ordinal1(X1,esk8_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_118,c_0_22])).

cnf(c_0_127,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_119])).

cnf(c_0_128,negated_conjecture,
    ( r2_hidden(esk9_0,esk8_0)
    | r1_tarski(esk2_3(esk8_0,k3_tarski(esk8_0),esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_120,c_0_121])).

cnf(c_0_129,negated_conjecture,
    ( r2_hidden(esk8_0,esk2_3(esk8_0,k3_tarski(esk8_0),esk8_0))
    | r2_hidden(esk9_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_122,c_0_112])).

cnf(c_0_130,negated_conjecture,
    ( r2_hidden(esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0),esk7_1(X1))
    | r2_hidden(esk7_1(X1),k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_123,c_0_124])).

cnf(c_0_131,negated_conjecture,
    ( r1_ordinal1(X1,esk8_0)
    | ~ v3_ordinal1(X1)
    | ~ r1_tarski(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_125,c_0_22])).

cnf(c_0_132,negated_conjecture,
    ( ~ r1_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_57]),c_0_127])).

cnf(c_0_133,negated_conjecture,
    ( r2_hidden(esk9_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_128]),c_0_129])).

cnf(c_0_134,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_95,c_0_48])).

cnf(c_0_135,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | ~ r2_hidden(X1,k1_ordinal1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_136,negated_conjecture,
    ( r2_hidden(esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0),X1)
    | r2_hidden(esk7_1(X1),k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_130]),c_0_127])).

cnf(c_0_137,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_57]),c_0_132])).

cnf(c_0_138,negated_conjecture,
    ( v3_ordinal1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_133])).

cnf(c_0_139,plain,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk7_1(X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_52])).

cnf(c_0_140,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_1(k2_xboole_0(esk8_0,k1_tarski(esk8_0))),X1),esk7_1(k2_xboole_0(esk8_0,k1_tarski(esk8_0))))
    | r2_hidden(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_134,c_0_88])).

cnf(c_0_141,negated_conjecture,
    ( r2_hidden(X1,k2_xboole_0(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k1_tarski(k2_xboole_0(esk8_0,k1_tarski(esk8_0)))))
    | ~ r1_ordinal1(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_118,c_0_57])).

cnf(c_0_142,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_135,c_0_43])).

cnf(c_0_143,negated_conjecture,
    ( r2_hidden(esk7_1(esk8_0),k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_136]),c_0_137])).

cnf(c_0_144,plain,
    ( X1 = k3_tarski(X1)
    | ~ v4_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_145,negated_conjecture,
    ( v4_ordinal1(esk8_0)
    | r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_133])).

cnf(c_0_146,negated_conjecture,
    ( v3_ordinal1(k2_xboole_0(esk9_0,k1_tarski(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_138])).

cnf(c_0_147,negated_conjecture,
    ( v3_ordinal1(esk1_2(esk7_1(k2_xboole_0(esk8_0,k1_tarski(esk8_0))),X1))
    | r2_hidden(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_139,c_0_140])).

cnf(c_0_148,negated_conjecture,
    ( r2_hidden(esk7_1(X1),k2_xboole_0(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k1_tarski(k2_xboole_0(esk8_0,k1_tarski(esk8_0)))))
    | ~ r1_ordinal1(esk7_1(X1),k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_141,c_0_52])).

cnf(c_0_149,negated_conjecture,
    ( r1_ordinal1(esk7_1(X1),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_57])).

cnf(c_0_150,negated_conjecture,
    ( esk7_1(esk8_0) = esk8_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_143]),c_0_61])).

cnf(c_0_151,negated_conjecture,
    ( k3_tarski(esk8_0) = esk8_0
    | r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_144,c_0_145])).

cnf(c_0_152,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(esk9_0,k1_tarski(esk9_0)))
    | ~ r1_ordinal1(X1,k2_xboole_0(esk9_0,k1_tarski(esk9_0)))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_146])).

cnf(c_0_153,negated_conjecture,
    ( v1_ordinal1(esk1_2(esk7_1(k2_xboole_0(esk8_0,k1_tarski(esk8_0))),X1))
    | r2_hidden(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_147])).

cnf(c_0_154,negated_conjecture,
    ( r2_hidden(esk7_1(X1),k2_xboole_0(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k1_tarski(k2_xboole_0(esk8_0,k1_tarski(esk8_0)))))
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),X1) ),
    inference(spm,[status(thm)],[c_0_148,c_0_149])).

cnf(c_0_155,negated_conjecture,
    ( r2_hidden(esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0),esk8_0)
    | r2_hidden(X1,esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_115,c_0_150])).

cnf(c_0_156,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)
    | r2_hidden(esk2_3(esk8_0,esk8_0,X1),esk8_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_111,c_0_151])).

cnf(c_0_157,negated_conjecture,
    ( r1_tarski(esk7_1(X1),k2_xboole_0(esk9_0,k1_tarski(esk9_0)))
    | ~ r1_ordinal1(esk7_1(X1),k2_xboole_0(esk9_0,k1_tarski(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_152,c_0_52])).

cnf(c_0_158,negated_conjecture,
    ( r1_ordinal1(esk7_1(X1),k2_xboole_0(esk9_0,k1_tarski(esk9_0)))
    | r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_146])).

cnf(c_0_159,negated_conjecture,
    ( r2_hidden(esk8_0,X1)
    | r1_tarski(X2,esk1_2(esk7_1(k2_xboole_0(esk8_0,k1_tarski(esk8_0))),X1))
    | ~ r2_hidden(X2,esk1_2(esk7_1(k2_xboole_0(esk8_0,k1_tarski(esk8_0))),X1)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_153])).

cnf(c_0_160,negated_conjecture,
    ( esk7_1(X1) = k2_xboole_0(esk8_0,k1_tarski(esk8_0))
    | r2_hidden(esk7_1(X1),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),X1) ),
    inference(spm,[status(thm)],[c_0_142,c_0_154])).

cnf(c_0_161,negated_conjecture,
    ( r2_hidden(esk9_0,esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0))
    | r2_hidden(esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_155,c_0_133])).

cnf(c_0_162,negated_conjecture,
    ( r2_hidden(esk2_3(esk8_0,esk8_0,esk9_0),esk8_0)
    | r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_156,c_0_133])).

cnf(c_0_163,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)
    | r2_hidden(X1,esk2_3(esk8_0,esk8_0,X1))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_122,c_0_151])).

cnf(c_0_164,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),X1)
    | r1_tarski(esk7_1(X1),k2_xboole_0(esk9_0,k1_tarski(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_157,c_0_158])).

cnf(c_0_165,negated_conjecture,
    ( r2_hidden(esk8_0,X1)
    | r1_tarski(X2,esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),X1))
    | ~ r2_hidden(X2,esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_159,c_0_160]),c_0_61]),c_0_127])).

cnf(c_0_166,negated_conjecture,
    ( r2_hidden(esk9_0,esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_161]),c_0_137])).

cnf(c_0_167,negated_conjecture,
    ( r2_hidden(esk2_3(esk8_0,esk8_0,esk9_0),esk8_0)
    | r2_hidden(X1,k3_tarski(esk8_0))
    | ~ r2_hidden(X1,k2_xboole_0(esk9_0,k1_tarski(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_162])).

cnf(c_0_168,negated_conjecture,
    ( r2_hidden(esk9_0,esk2_3(esk8_0,esk8_0,esk9_0))
    | r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_163,c_0_133])).

cnf(c_0_169,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),X1)
    | r2_hidden(X2,k2_xboole_0(esk9_0,k1_tarski(esk9_0)))
    | ~ r2_hidden(X2,esk7_1(X1)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_164])).

cnf(c_0_170,negated_conjecture,
    ( r1_tarski(esk9_0,esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_166]),c_0_127])).

cnf(c_0_171,negated_conjecture,
    ( r2_hidden(esk2_3(esk8_0,esk8_0,esk9_0),esk8_0)
    | r2_hidden(esk9_0,k3_tarski(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_167,c_0_58])).

cnf(c_0_172,negated_conjecture,
    ( r2_hidden(esk9_0,esk2_3(esk8_0,esk8_0,esk9_0))
    | r2_hidden(X1,k3_tarski(esk8_0))
    | ~ r2_hidden(X1,k2_xboole_0(esk9_0,k1_tarski(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_168])).

cnf(c_0_173,negated_conjecture,
    ( r2_hidden(esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0),k2_xboole_0(esk9_0,k1_tarski(esk9_0)))
    | r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_169,c_0_124])).

cnf(c_0_174,negated_conjecture,
    ( ~ r2_hidden(esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_170])).

cnf(c_0_175,negated_conjecture,
    ( r2_hidden(esk9_0,k3_tarski(esk8_0))
    | r2_hidden(X1,k3_tarski(esk8_0))
    | ~ r2_hidden(X1,esk2_3(esk8_0,esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_171])).

cnf(c_0_176,negated_conjecture,
    ( r2_hidden(esk9_0,esk2_3(esk8_0,esk8_0,esk9_0))
    | r2_hidden(esk9_0,k3_tarski(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_172,c_0_58])).

cnf(c_0_177,negated_conjecture,
    ( esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0) = esk9_0
    | r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_173]),c_0_174])).

cnf(c_0_178,negated_conjecture,
    ( r2_hidden(esk9_0,k3_tarski(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_175,c_0_176])).

cnf(c_0_179,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(esk9_0,k1_tarski(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_146])).

cnf(c_0_180,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_177]),c_0_133])]),c_0_137])).

cnf(c_0_181,negated_conjecture,
    ( r2_hidden(esk2_3(esk8_0,k3_tarski(esk8_0),esk9_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_111,c_0_178])).

cnf(c_0_182,negated_conjecture,
    ( r1_ordinal1(X1,esk9_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk9_0,k1_tarski(esk9_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_138]),c_0_179])).

cnf(c_0_183,negated_conjecture,
    ( k2_xboole_0(esk9_0,k1_tarski(esk9_0)) = esk8_0
    | r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_142,c_0_180])).

cnf(c_0_184,negated_conjecture,
    ( r1_tarski(X1,esk9_0)
    | ~ r1_ordinal1(X1,esk9_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_138])).

cnf(c_0_185,negated_conjecture,
    ( v3_ordinal1(esk2_3(esk8_0,k3_tarski(esk8_0),esk9_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_181])).

cnf(c_0_186,negated_conjecture,
    ( r1_ordinal1(X1,esk9_0)
    | r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_182,c_0_183])).

cnf(c_0_187,negated_conjecture,
    ( ~ r2_hidden(k1_ordinal1(esk9_0),esk8_0)
    | ~ v4_ordinal1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_188,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_189,negated_conjecture,
    ( r1_tarski(esk2_3(esk8_0,k3_tarski(esk8_0),esk9_0),esk9_0)
    | ~ r1_ordinal1(esk2_3(esk8_0,k3_tarski(esk8_0),esk9_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_184,c_0_185])).

cnf(c_0_190,negated_conjecture,
    ( r1_ordinal1(esk2_3(esk8_0,k3_tarski(esk8_0),esk9_0),esk9_0)
    | r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_186,c_0_181])).

cnf(c_0_191,negated_conjecture,
    ( ~ v4_ordinal1(esk8_0)
    | ~ r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0) ),
    inference(rw,[status(thm)],[c_0_187,c_0_43])).

cnf(c_0_192,plain,
    ( v4_ordinal1(X1)
    | r2_hidden(esk4_2(X1,X1),X1)
    | r2_hidden(esk3_2(X1,X1),X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_188])])).

cnf(c_0_193,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)
    | r1_tarski(esk2_3(esk8_0,k3_tarski(esk8_0),esk9_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_189,c_0_190])).

cnf(c_0_194,negated_conjecture,
    ( r2_hidden(esk9_0,esk2_3(esk8_0,k3_tarski(esk8_0),esk9_0)) ),
    inference(spm,[status(thm)],[c_0_122,c_0_178])).

cnf(c_0_195,negated_conjecture,
    ( r2_hidden(esk3_2(esk8_0,esk8_0),esk8_0)
    | r2_hidden(esk4_2(esk8_0,esk8_0),esk8_0)
    | ~ r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_191,c_0_192])).

cnf(c_0_196,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_193]),c_0_194])])).

cnf(c_0_197,plain,
    ( r2_hidden(esk3_2(X1,X2),esk4_2(X1,X2))
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_198,negated_conjecture,
    ( r2_hidden(esk4_2(esk8_0,esk8_0),esk8_0)
    | r2_hidden(esk3_2(esk8_0,esk8_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_195,c_0_196])])).

cnf(c_0_199,plain,
    ( v4_ordinal1(X1)
    | r2_hidden(esk3_2(X1,X1),esk4_2(X1,X1))
    | r2_hidden(esk3_2(X1,X1),X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_197])])).

cnf(c_0_200,negated_conjecture,
    ( r2_hidden(esk8_0,k3_tarski(esk8_0))
    | r2_hidden(k3_tarski(esk8_0),esk8_0)
    | r2_hidden(esk6_1(esk8_0),esk8_0)
    | ~ r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_191,c_0_32])).

cnf(c_0_201,negated_conjecture,
    ( r2_hidden(esk3_2(esk8_0,esk8_0),esk8_0)
    | r1_tarski(esk4_2(esk8_0,esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_120,c_0_198])).

cnf(c_0_202,negated_conjecture,
    ( r2_hidden(esk3_2(esk8_0,esk8_0),esk4_2(esk8_0,esk8_0))
    | r2_hidden(esk3_2(esk8_0,esk8_0),esk8_0)
    | ~ r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_191,c_0_199])).

cnf(c_0_203,negated_conjecture,
    ( r2_hidden(esk6_1(esk8_0),esk8_0)
    | r2_hidden(k3_tarski(esk8_0),esk8_0)
    | r2_hidden(esk8_0,k3_tarski(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_200,c_0_196])])).

cnf(c_0_204,negated_conjecture,
    ( r2_hidden(esk3_2(esk8_0,esk8_0),esk8_0)
    | r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X1,esk4_2(esk8_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_201])).

cnf(c_0_205,negated_conjecture,
    ( r2_hidden(esk3_2(esk8_0,esk8_0),esk4_2(esk8_0,esk8_0))
    | r2_hidden(esk3_2(esk8_0,esk8_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_202,c_0_196])])).

cnf(c_0_206,negated_conjecture,
    ( v3_ordinal1(esk6_1(esk8_0))
    | r2_hidden(esk8_0,k3_tarski(esk8_0))
    | r2_hidden(k3_tarski(esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_203])).

cnf(c_0_207,negated_conjecture,
    ( r2_hidden(esk3_2(esk8_0,esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_204,c_0_205])).

cnf(c_0_208,negated_conjecture,
    ( ~ v4_ordinal1(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_191,c_0_196])])).

cnf(c_0_209,negated_conjecture,
    ( v3_ordinal1(k3_tarski(esk8_0))
    | r2_hidden(esk8_0,k3_tarski(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_206]),c_0_33])).

cnf(c_0_210,plain,
    ( X2 = k3_tarski(X1)
    | ~ r2_hidden(esk3_2(X1,X2),X2)
    | ~ r2_hidden(esk3_2(X1,X2),X3)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_211,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk3_2(esk8_0,esk8_0),k1_tarski(esk3_2(esk8_0,esk8_0))),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_207]),c_0_208])).

cnf(c_0_212,negated_conjecture,
    ( k3_tarski(esk8_0) = esk8_0
    | r2_hidden(esk8_0,k3_tarski(esk8_0))
    | r2_hidden(k3_tarski(esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_209])).

cnf(c_0_213,negated_conjecture,
    ( X1 = k3_tarski(esk8_0)
    | ~ r2_hidden(esk3_2(esk8_0,X1),k2_xboole_0(esk3_2(esk8_0,esk8_0),k1_tarski(esk3_2(esk8_0,esk8_0))))
    | ~ r2_hidden(esk3_2(esk8_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_210,c_0_211])).

cnf(c_0_214,negated_conjecture,
    ( r2_hidden(k3_tarski(esk8_0),esk8_0)
    | r2_hidden(esk8_0,k3_tarski(esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_212]),c_0_208])).

cnf(c_0_215,negated_conjecture,
    ( k3_tarski(esk8_0) = esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_213,c_0_207]),c_0_58])])).

cnf(c_0_216,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_214,c_0_215]),c_0_215])]),c_0_127]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 10.07/10.24  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 10.07/10.24  # and selection function SelectCQIArEqFirst.
% 10.07/10.24  #
% 10.07/10.24  # Preprocessing time       : 0.029 s
% 10.07/10.24  # Presaturation interreduction done
% 10.07/10.24  
% 10.07/10.24  # Proof found!
% 10.07/10.24  # SZS status Theorem
% 10.07/10.24  # SZS output start CNFRefutation
% 10.07/10.24  fof(t41_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_ordinal1)).
% 10.07/10.24  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 10.07/10.24  fof(t35_ordinal1, axiom, ![X1]:(![X2]:(r2_hidden(X2,X1)=>v3_ordinal1(X2))=>v3_ordinal1(k3_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_ordinal1)).
% 10.07/10.24  fof(d6_ordinal1, axiom, ![X1]:(v4_ordinal1(X1)<=>X1=k3_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_ordinal1)).
% 10.07/10.24  fof(t23_ordinal1, axiom, ![X1, X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>v3_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_ordinal1)).
% 10.07/10.25  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 10.07/10.25  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 10.07/10.25  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 10.07/10.25  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 10.07/10.25  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 10.07/10.25  fof(t39_ordinal1, axiom, ![X1]:?[X2]:((v3_ordinal1(X2)&~(r2_hidden(X2,X1)))&![X3]:(v3_ordinal1(X3)=>(~(r2_hidden(X3,X1))=>r1_ordinal1(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_ordinal1)).
% 10.07/10.25  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 10.07/10.25  fof(cc1_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(v1_ordinal1(X1)&v2_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 10.07/10.25  fof(t13_ordinal1, axiom, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 10.07/10.25  fof(t34_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 10.07/10.25  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 10.07/10.25  fof(d2_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)<=>![X2]:(r2_hidden(X2,X1)=>r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 10.07/10.25  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.07/10.25  fof(c_0_18, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1)))))), inference(assume_negation,[status(cth)],[t41_ordinal1])).
% 10.07/10.25  fof(c_0_19, plain, ![X40, X41]:(~v3_ordinal1(X40)|(~v3_ordinal1(X41)|(r2_hidden(X40,X41)|X40=X41|r2_hidden(X41,X40)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 10.07/10.25  fof(c_0_20, negated_conjecture, ![X54]:(v3_ordinal1(esk8_0)&(((v3_ordinal1(esk9_0)|~v4_ordinal1(esk8_0))&((r2_hidden(esk9_0,esk8_0)|~v4_ordinal1(esk8_0))&(~r2_hidden(k1_ordinal1(esk9_0),esk8_0)|~v4_ordinal1(esk8_0))))&(v4_ordinal1(esk8_0)|(~v3_ordinal1(X54)|(~r2_hidden(X54,esk8_0)|r2_hidden(k1_ordinal1(X54),esk8_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])])])).
% 10.07/10.25  cnf(c_0_21, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 10.07/10.25  cnf(c_0_22, negated_conjecture, (v3_ordinal1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 10.07/10.25  fof(c_0_23, plain, ![X45]:((r2_hidden(esk6_1(X45),X45)|v3_ordinal1(k3_tarski(X45)))&(~v3_ordinal1(esk6_1(X45))|v3_ordinal1(k3_tarski(X45)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_ordinal1])])])])).
% 10.07/10.25  fof(c_0_24, plain, ![X32]:((~v4_ordinal1(X32)|X32=k3_tarski(X32))&(X32!=k3_tarski(X32)|v4_ordinal1(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_ordinal1])])).
% 10.07/10.25  cnf(c_0_25, negated_conjecture, (X1=esk8_0|r2_hidden(X1,esk8_0)|r2_hidden(esk8_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 10.07/10.25  cnf(c_0_26, plain, (r2_hidden(esk6_1(X1),X1)|v3_ordinal1(k3_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 10.07/10.25  fof(c_0_27, plain, ![X38, X39]:(~v3_ordinal1(X39)|(~r2_hidden(X38,X39)|v3_ordinal1(X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).
% 10.07/10.25  cnf(c_0_28, plain, (v4_ordinal1(X1)|X1!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 10.07/10.25  cnf(c_0_29, negated_conjecture, (k3_tarski(X1)=esk8_0|r2_hidden(esk8_0,k3_tarski(X1))|r2_hidden(k3_tarski(X1),esk8_0)|r2_hidden(esk6_1(X1),X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 10.07/10.25  cnf(c_0_30, plain, (v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 10.07/10.25  cnf(c_0_31, negated_conjecture, (r2_hidden(esk9_0,esk8_0)|~v4_ordinal1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 10.07/10.25  cnf(c_0_32, negated_conjecture, (v4_ordinal1(esk8_0)|r2_hidden(esk6_1(esk8_0),esk8_0)|r2_hidden(k3_tarski(esk8_0),esk8_0)|r2_hidden(esk8_0,k3_tarski(esk8_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29])])).
% 10.07/10.25  cnf(c_0_33, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_30, c_0_22])).
% 10.07/10.25  cnf(c_0_34, negated_conjecture, (r2_hidden(esk8_0,k3_tarski(esk8_0))|r2_hidden(k3_tarski(esk8_0),esk8_0)|r2_hidden(esk6_1(esk8_0),esk8_0)|r2_hidden(esk9_0,esk8_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 10.07/10.25  cnf(c_0_35, plain, (v3_ordinal1(k3_tarski(X1))|~v3_ordinal1(esk6_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 10.07/10.25  cnf(c_0_36, negated_conjecture, (v3_ordinal1(esk6_1(esk8_0))|r2_hidden(k3_tarski(esk8_0),esk8_0)|r2_hidden(esk8_0,k3_tarski(esk8_0))|r2_hidden(esk9_0,esk8_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 10.07/10.25  fof(c_0_37, plain, ![X42]:(~v3_ordinal1(X42)|v3_ordinal1(k1_ordinal1(X42))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 10.07/10.25  fof(c_0_38, plain, ![X27]:k1_ordinal1(X27)=k2_xboole_0(X27,k1_tarski(X27)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 10.07/10.25  fof(c_0_39, plain, ![X50, X51]:(~r2_hidden(X50,X51)|~r1_tarski(X51,X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 10.07/10.25  fof(c_0_40, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 10.07/10.25  cnf(c_0_41, negated_conjecture, (v3_ordinal1(k3_tarski(esk8_0))|r2_hidden(esk8_0,k3_tarski(esk8_0))|r2_hidden(esk9_0,esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_33])).
% 10.07/10.25  cnf(c_0_42, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 10.07/10.25  cnf(c_0_43, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 10.07/10.25  fof(c_0_44, plain, ![X35]:r2_hidden(X35,k1_ordinal1(X35)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 10.07/10.25  fof(c_0_45, plain, ![X47, X49]:((v3_ordinal1(esk7_1(X47))&~r2_hidden(esk7_1(X47),X47))&(~v3_ordinal1(X49)|(r2_hidden(X49,X47)|r1_ordinal1(esk7_1(X47),X49)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_ordinal1])])])])])).
% 10.07/10.25  cnf(c_0_46, negated_conjecture, (v4_ordinal1(esk8_0)|r2_hidden(k1_ordinal1(X1),esk8_0)|~v3_ordinal1(X1)|~r2_hidden(X1,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 10.07/10.25  cnf(c_0_47, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 10.07/10.25  cnf(c_0_48, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 10.07/10.25  cnf(c_0_49, negated_conjecture, (k3_tarski(esk8_0)=esk8_0|r2_hidden(esk8_0,k3_tarski(esk8_0))|r2_hidden(k3_tarski(esk8_0),esk8_0)|r2_hidden(esk9_0,esk8_0)), inference(spm,[status(thm)],[c_0_25, c_0_41])).
% 10.07/10.25  cnf(c_0_50, plain, (v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 10.07/10.25  cnf(c_0_51, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 10.07/10.25  cnf(c_0_52, plain, (v3_ordinal1(esk7_1(X1))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 10.07/10.25  fof(c_0_53, plain, ![X13, X14, X15, X17, X18, X19, X20, X22]:((((r2_hidden(X15,esk2_3(X13,X14,X15))|~r2_hidden(X15,X14)|X14!=k3_tarski(X13))&(r2_hidden(esk2_3(X13,X14,X15),X13)|~r2_hidden(X15,X14)|X14!=k3_tarski(X13)))&(~r2_hidden(X17,X18)|~r2_hidden(X18,X13)|r2_hidden(X17,X14)|X14!=k3_tarski(X13)))&((~r2_hidden(esk3_2(X19,X20),X20)|(~r2_hidden(esk3_2(X19,X20),X22)|~r2_hidden(X22,X19))|X20=k3_tarski(X19))&((r2_hidden(esk3_2(X19,X20),esk4_2(X19,X20))|r2_hidden(esk3_2(X19,X20),X20)|X20=k3_tarski(X19))&(r2_hidden(esk4_2(X19,X20),X19)|r2_hidden(esk3_2(X19,X20),X20)|X20=k3_tarski(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 10.07/10.25  cnf(c_0_54, negated_conjecture, (v4_ordinal1(esk8_0)|r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk8_0)|~v3_ordinal1(X1)|~r2_hidden(X1,esk8_0)), inference(rw,[status(thm)],[c_0_46, c_0_43])).
% 10.07/10.25  cnf(c_0_55, plain, (r2_hidden(esk1_2(X1,X2),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 10.07/10.25  cnf(c_0_56, negated_conjecture, (r2_hidden(k3_tarski(esk8_0),esk8_0)|r2_hidden(esk8_0,k3_tarski(esk8_0))|r2_hidden(esk9_0,esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_49]), c_0_31])).
% 10.07/10.25  cnf(c_0_57, negated_conjecture, (v3_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_50, c_0_22])).
% 10.07/10.25  cnf(c_0_58, plain, (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_51, c_0_43])).
% 10.07/10.25  fof(c_0_59, plain, ![X24]:((v1_ordinal1(X24)|~v3_ordinal1(X24))&(v2_ordinal1(X24)|~v3_ordinal1(X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).
% 10.07/10.25  fof(c_0_60, plain, ![X36, X37]:((~r2_hidden(X36,k1_ordinal1(X37))|(r2_hidden(X36,X37)|X36=X37))&((~r2_hidden(X36,X37)|r2_hidden(X36,k1_ordinal1(X37)))&(X36!=X37|r2_hidden(X36,k1_ordinal1(X37))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).
% 10.07/10.25  cnf(c_0_61, plain, (~r2_hidden(esk7_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 10.07/10.25  cnf(c_0_62, negated_conjecture, (esk7_1(X1)=esk8_0|r2_hidden(esk8_0,esk7_1(X1))|r2_hidden(esk7_1(X1),esk8_0)), inference(spm,[status(thm)],[c_0_25, c_0_52])).
% 10.07/10.25  fof(c_0_63, plain, ![X43, X44]:((~r2_hidden(X43,k1_ordinal1(X44))|r1_ordinal1(X43,X44)|~v3_ordinal1(X44)|~v3_ordinal1(X43))&(~r1_ordinal1(X43,X44)|r2_hidden(X43,k1_ordinal1(X44))|~v3_ordinal1(X44)|~v3_ordinal1(X43))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).
% 10.07/10.25  cnf(c_0_64, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 10.07/10.25  cnf(c_0_65, negated_conjecture, (v4_ordinal1(esk8_0)|r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk8_0)|~r2_hidden(X1,esk8_0)), inference(csr,[status(thm)],[c_0_54, c_0_33])).
% 10.07/10.25  cnf(c_0_66, negated_conjecture, (r2_hidden(esk1_2(esk8_0,k3_tarski(esk8_0)),esk8_0)|r2_hidden(esk8_0,k3_tarski(esk8_0))|r2_hidden(esk9_0,esk8_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 10.07/10.25  fof(c_0_67, plain, ![X33, X34]:((~r1_ordinal1(X33,X34)|r1_tarski(X33,X34)|(~v3_ordinal1(X33)|~v3_ordinal1(X34)))&(~r1_tarski(X33,X34)|r1_ordinal1(X33,X34)|(~v3_ordinal1(X33)|~v3_ordinal1(X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 10.07/10.25  cnf(c_0_68, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_30, c_0_57])).
% 10.07/10.25  cnf(c_0_69, plain, (r2_hidden(esk1_2(k2_xboole_0(X1,k1_tarski(X1)),X1),k2_xboole_0(X1,k1_tarski(X1)))), inference(spm,[status(thm)],[c_0_55, c_0_58])).
% 10.07/10.25  fof(c_0_70, plain, ![X28, X29, X30]:((~v1_ordinal1(X28)|(~r2_hidden(X29,X28)|r1_tarski(X29,X28)))&((r2_hidden(esk5_1(X30),X30)|v1_ordinal1(X30))&(~r1_tarski(esk5_1(X30),X30)|v1_ordinal1(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).
% 10.07/10.25  cnf(c_0_71, plain, (v1_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 10.07/10.25  cnf(c_0_72, plain, (r2_hidden(X1,k1_ordinal1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 10.07/10.25  cnf(c_0_73, negated_conjecture, (r2_hidden(esk7_1(X1),esk8_0)|r2_hidden(esk8_0,esk7_1(X1))|~r2_hidden(esk8_0,X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 10.07/10.25  cnf(c_0_74, plain, (r1_ordinal1(X1,X2)|~r2_hidden(X1,k1_ordinal1(X2))|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 10.07/10.25  cnf(c_0_75, plain, (r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X3,X2)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_64])).
% 10.07/10.25  cnf(c_0_76, negated_conjecture, (r2_hidden(k2_xboole_0(esk1_2(esk8_0,k3_tarski(esk8_0)),k1_tarski(esk1_2(esk8_0,k3_tarski(esk8_0)))),esk8_0)|r2_hidden(esk8_0,k3_tarski(esk8_0))|r2_hidden(esk9_0,esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_31])).
% 10.07/10.25  cnf(c_0_77, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 10.07/10.25  cnf(c_0_78, negated_conjecture, (v3_ordinal1(esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 10.07/10.25  cnf(c_0_79, plain, (r1_tarski(X2,X1)|~v1_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 10.07/10.25  cnf(c_0_80, plain, (v1_ordinal1(esk7_1(X1))), inference(spm,[status(thm)],[c_0_71, c_0_52])).
% 10.07/10.25  cnf(c_0_81, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_72, c_0_43])).
% 10.07/10.25  cnf(c_0_82, negated_conjecture, (r2_hidden(esk8_0,esk7_1(k2_xboole_0(esk8_0,k1_tarski(esk8_0))))|r2_hidden(esk7_1(k2_xboole_0(esk8_0,k1_tarski(esk8_0))),esk8_0)), inference(spm,[status(thm)],[c_0_73, c_0_58])).
% 10.07/10.25  cnf(c_0_83, plain, (r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_74, c_0_43])).
% 10.07/10.25  cnf(c_0_84, negated_conjecture, (r2_hidden(esk8_0,k3_tarski(esk8_0))|r2_hidden(X1,k3_tarski(esk8_0))|r2_hidden(esk9_0,esk8_0)|~r2_hidden(X1,k2_xboole_0(esk1_2(esk8_0,k3_tarski(esk8_0)),k1_tarski(esk1_2(esk8_0,k3_tarski(esk8_0)))))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 10.07/10.25  cnf(c_0_85, negated_conjecture, (r1_tarski(X1,esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0))|~r1_ordinal1(X1,esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 10.07/10.25  cnf(c_0_86, plain, (r2_hidden(X1,X2)|r1_ordinal1(esk7_1(X2),X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 10.07/10.25  cnf(c_0_87, plain, (r1_tarski(X1,esk7_1(X2))|~r2_hidden(X1,esk7_1(X2))), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 10.07/10.25  cnf(c_0_88, negated_conjecture, (r2_hidden(esk8_0,esk7_1(k2_xboole_0(esk8_0,k1_tarski(esk8_0))))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_61])).
% 10.07/10.25  cnf(c_0_89, negated_conjecture, (r1_ordinal1(X1,esk8_0)|~r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_22]), c_0_68])).
% 10.07/10.25  cnf(c_0_90, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 10.07/10.25  cnf(c_0_91, negated_conjecture, (r2_hidden(esk1_2(esk8_0,k3_tarski(esk8_0)),k3_tarski(esk8_0))|r2_hidden(esk8_0,k3_tarski(esk8_0))|r2_hidden(esk9_0,esk8_0)), inference(spm,[status(thm)],[c_0_84, c_0_58])).
% 10.07/10.25  cnf(c_0_92, plain, (r1_tarski(X1,esk7_1(X2))|~r1_ordinal1(X1,esk7_1(X2))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_77, c_0_52])).
% 10.07/10.25  cnf(c_0_93, negated_conjecture, (r1_tarski(esk7_1(X1),esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0))|~r1_ordinal1(esk7_1(X1),esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0))), inference(spm,[status(thm)],[c_0_85, c_0_52])).
% 10.07/10.25  cnf(c_0_94, negated_conjecture, (r1_ordinal1(esk7_1(X1),esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0))|r2_hidden(esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0),X1)), inference(spm,[status(thm)],[c_0_86, c_0_78])).
% 10.07/10.25  cnf(c_0_95, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 10.07/10.25  cnf(c_0_96, negated_conjecture, (r1_tarski(esk8_0,esk7_1(k2_xboole_0(esk8_0,k1_tarski(esk8_0))))), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 10.07/10.25  cnf(c_0_97, negated_conjecture, (r1_tarski(X1,esk8_0)|~r1_ordinal1(X1,esk8_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_77, c_0_22])).
% 10.07/10.25  cnf(c_0_98, negated_conjecture, (r1_ordinal1(esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_89, c_0_69])).
% 10.07/10.25  fof(c_0_99, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 10.07/10.25  cnf(c_0_100, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|X2!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 10.07/10.25  cnf(c_0_101, negated_conjecture, (r2_hidden(esk8_0,k3_tarski(esk8_0))|r2_hidden(esk9_0,esk8_0)|r1_tarski(esk8_0,k3_tarski(esk8_0))), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 10.07/10.25  cnf(c_0_102, plain, (r1_tarski(esk7_1(X1),esk7_1(X2))|~r1_ordinal1(esk7_1(X1),esk7_1(X2))), inference(spm,[status(thm)],[c_0_92, c_0_52])).
% 10.07/10.25  cnf(c_0_103, plain, (r1_ordinal1(esk7_1(X1),esk7_1(X2))|r2_hidden(esk7_1(X2),X1)), inference(spm,[status(thm)],[c_0_86, c_0_52])).
% 10.07/10.25  cnf(c_0_104, negated_conjecture, (r2_hidden(esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0),X1)|r1_tarski(esk7_1(X1),esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0))), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 10.07/10.25  cnf(c_0_105, negated_conjecture, (r2_hidden(X1,esk7_1(k2_xboole_0(esk8_0,k1_tarski(esk8_0))))|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 10.07/10.25  cnf(c_0_106, negated_conjecture, (r2_hidden(esk8_0,esk7_1(esk7_1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)))))|r2_hidden(esk7_1(esk7_1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)))),esk8_0)), inference(spm,[status(thm)],[c_0_73, c_0_88])).
% 10.07/10.25  cnf(c_0_107, negated_conjecture, (r1_tarski(esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_78]), c_0_98])])).
% 10.07/10.25  cnf(c_0_108, plain, (r2_hidden(X1,k1_ordinal1(X2))|~r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 10.07/10.25  cnf(c_0_109, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_99])).
% 10.07/10.25  cnf(c_0_110, negated_conjecture, (v1_ordinal1(esk8_0)), inference(spm,[status(thm)],[c_0_71, c_0_22])).
% 10.07/10.25  cnf(c_0_111, plain, (r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)|~r2_hidden(X2,k3_tarski(X1))), inference(er,[status(thm)],[c_0_100])).
% 10.07/10.25  cnf(c_0_112, negated_conjecture, (r2_hidden(esk8_0,k3_tarski(esk8_0))|r2_hidden(esk9_0,esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_101]), c_0_56])).
% 10.07/10.25  cnf(c_0_113, plain, (r2_hidden(X1,esk2_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k3_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 10.07/10.25  cnf(c_0_114, plain, (r2_hidden(esk7_1(X1),X2)|r1_tarski(esk7_1(X2),esk7_1(X1))), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 10.07/10.25  cnf(c_0_115, negated_conjecture, (r2_hidden(esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0),X1)|r2_hidden(X2,esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0))|~r2_hidden(X2,esk7_1(X1))), inference(spm,[status(thm)],[c_0_95, c_0_104])).
% 10.07/10.25  cnf(c_0_116, negated_conjecture, (r2_hidden(esk8_0,esk7_1(esk7_1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)))))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_61])).
% 10.07/10.25  cnf(c_0_117, negated_conjecture, (~r2_hidden(esk8_0,esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0))), inference(spm,[status(thm)],[c_0_47, c_0_107])).
% 10.07/10.25  cnf(c_0_118, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r1_ordinal1(X1,X2)), inference(rw,[status(thm)],[c_0_108, c_0_43])).
% 10.07/10.25  cnf(c_0_119, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_109])).
% 10.07/10.25  cnf(c_0_120, negated_conjecture, (r1_tarski(X1,esk8_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_79, c_0_110])).
% 10.07/10.25  cnf(c_0_121, negated_conjecture, (r2_hidden(esk2_3(esk8_0,k3_tarski(esk8_0),esk8_0),esk8_0)|r2_hidden(esk9_0,esk8_0)), inference(spm,[status(thm)],[c_0_111, c_0_112])).
% 10.07/10.25  cnf(c_0_122, plain, (r2_hidden(X1,esk2_3(X2,k3_tarski(X2),X1))|~r2_hidden(X1,k3_tarski(X2))), inference(er,[status(thm)],[c_0_113])).
% 10.07/10.25  cnf(c_0_123, plain, (r2_hidden(esk7_1(X1),X2)|r2_hidden(X3,esk7_1(X1))|~r2_hidden(X3,esk7_1(X2))), inference(spm,[status(thm)],[c_0_95, c_0_114])).
% 10.07/10.25  cnf(c_0_124, negated_conjecture, (r2_hidden(esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0),esk7_1(k2_xboole_0(esk8_0,k1_tarski(esk8_0))))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_117])).
% 10.07/10.25  cnf(c_0_125, plain, (r1_ordinal1(X1,X2)|~r1_tarski(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 10.07/10.25  cnf(c_0_126, negated_conjecture, (r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|~r1_ordinal1(X1,esk8_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_118, c_0_22])).
% 10.07/10.25  cnf(c_0_127, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_47, c_0_119])).
% 10.07/10.25  cnf(c_0_128, negated_conjecture, (r2_hidden(esk9_0,esk8_0)|r1_tarski(esk2_3(esk8_0,k3_tarski(esk8_0),esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_120, c_0_121])).
% 10.07/10.25  cnf(c_0_129, negated_conjecture, (r2_hidden(esk8_0,esk2_3(esk8_0,k3_tarski(esk8_0),esk8_0))|r2_hidden(esk9_0,esk8_0)), inference(spm,[status(thm)],[c_0_122, c_0_112])).
% 10.07/10.25  cnf(c_0_130, negated_conjecture, (r2_hidden(esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0),esk7_1(X1))|r2_hidden(esk7_1(X1),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_123, c_0_124])).
% 10.07/10.25  cnf(c_0_131, negated_conjecture, (r1_ordinal1(X1,esk8_0)|~v3_ordinal1(X1)|~r1_tarski(X1,esk8_0)), inference(spm,[status(thm)],[c_0_125, c_0_22])).
% 10.07/10.25  cnf(c_0_132, negated_conjecture, (~r1_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_57]), c_0_127])).
% 10.07/10.25  cnf(c_0_133, negated_conjecture, (r2_hidden(esk9_0,esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_128]), c_0_129])).
% 10.07/10.25  cnf(c_0_134, plain, (r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_95, c_0_48])).
% 10.07/10.25  cnf(c_0_135, plain, (r2_hidden(X1,X2)|X1=X2|~r2_hidden(X1,k1_ordinal1(X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 10.07/10.25  cnf(c_0_136, negated_conjecture, (r2_hidden(esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0),X1)|r2_hidden(esk7_1(X1),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_130]), c_0_127])).
% 10.07/10.25  cnf(c_0_137, negated_conjecture, (~r1_tarski(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_57]), c_0_132])).
% 10.07/10.25  cnf(c_0_138, negated_conjecture, (v3_ordinal1(esk9_0)), inference(spm,[status(thm)],[c_0_33, c_0_133])).
% 10.07/10.25  cnf(c_0_139, plain, (v3_ordinal1(X1)|~r2_hidden(X1,esk7_1(X2))), inference(spm,[status(thm)],[c_0_30, c_0_52])).
% 10.07/10.25  cnf(c_0_140, negated_conjecture, (r2_hidden(esk1_2(esk7_1(k2_xboole_0(esk8_0,k1_tarski(esk8_0))),X1),esk7_1(k2_xboole_0(esk8_0,k1_tarski(esk8_0))))|r2_hidden(esk8_0,X1)), inference(spm,[status(thm)],[c_0_134, c_0_88])).
% 10.07/10.25  cnf(c_0_141, negated_conjecture, (r2_hidden(X1,k2_xboole_0(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k1_tarski(k2_xboole_0(esk8_0,k1_tarski(esk8_0)))))|~r1_ordinal1(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_118, c_0_57])).
% 10.07/10.25  cnf(c_0_142, plain, (X1=X2|r2_hidden(X1,X2)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_135, c_0_43])).
% 10.07/10.25  cnf(c_0_143, negated_conjecture, (r2_hidden(esk7_1(esk8_0),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_136]), c_0_137])).
% 10.07/10.25  cnf(c_0_144, plain, (X1=k3_tarski(X1)|~v4_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 10.07/10.25  cnf(c_0_145, negated_conjecture, (v4_ordinal1(esk8_0)|r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)), inference(spm,[status(thm)],[c_0_65, c_0_133])).
% 10.07/10.25  cnf(c_0_146, negated_conjecture, (v3_ordinal1(k2_xboole_0(esk9_0,k1_tarski(esk9_0)))), inference(spm,[status(thm)],[c_0_50, c_0_138])).
% 10.07/10.25  cnf(c_0_147, negated_conjecture, (v3_ordinal1(esk1_2(esk7_1(k2_xboole_0(esk8_0,k1_tarski(esk8_0))),X1))|r2_hidden(esk8_0,X1)), inference(spm,[status(thm)],[c_0_139, c_0_140])).
% 10.07/10.25  cnf(c_0_148, negated_conjecture, (r2_hidden(esk7_1(X1),k2_xboole_0(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k1_tarski(k2_xboole_0(esk8_0,k1_tarski(esk8_0)))))|~r1_ordinal1(esk7_1(X1),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_141, c_0_52])).
% 10.07/10.25  cnf(c_0_149, negated_conjecture, (r1_ordinal1(esk7_1(X1),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),X1)), inference(spm,[status(thm)],[c_0_86, c_0_57])).
% 10.07/10.25  cnf(c_0_150, negated_conjecture, (esk7_1(esk8_0)=esk8_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_143]), c_0_61])).
% 10.07/10.25  cnf(c_0_151, negated_conjecture, (k3_tarski(esk8_0)=esk8_0|r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)), inference(spm,[status(thm)],[c_0_144, c_0_145])).
% 10.07/10.25  cnf(c_0_152, negated_conjecture, (r1_tarski(X1,k2_xboole_0(esk9_0,k1_tarski(esk9_0)))|~r1_ordinal1(X1,k2_xboole_0(esk9_0,k1_tarski(esk9_0)))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_77, c_0_146])).
% 10.07/10.25  cnf(c_0_153, negated_conjecture, (v1_ordinal1(esk1_2(esk7_1(k2_xboole_0(esk8_0,k1_tarski(esk8_0))),X1))|r2_hidden(esk8_0,X1)), inference(spm,[status(thm)],[c_0_71, c_0_147])).
% 10.07/10.25  cnf(c_0_154, negated_conjecture, (r2_hidden(esk7_1(X1),k2_xboole_0(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k1_tarski(k2_xboole_0(esk8_0,k1_tarski(esk8_0)))))|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),X1)), inference(spm,[status(thm)],[c_0_148, c_0_149])).
% 10.07/10.25  cnf(c_0_155, negated_conjecture, (r2_hidden(esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0),esk8_0)|r2_hidden(X1,esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0))|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_115, c_0_150])).
% 10.07/10.25  cnf(c_0_156, negated_conjecture, (r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)|r2_hidden(esk2_3(esk8_0,esk8_0,X1),esk8_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_111, c_0_151])).
% 10.07/10.25  cnf(c_0_157, negated_conjecture, (r1_tarski(esk7_1(X1),k2_xboole_0(esk9_0,k1_tarski(esk9_0)))|~r1_ordinal1(esk7_1(X1),k2_xboole_0(esk9_0,k1_tarski(esk9_0)))), inference(spm,[status(thm)],[c_0_152, c_0_52])).
% 10.07/10.25  cnf(c_0_158, negated_conjecture, (r1_ordinal1(esk7_1(X1),k2_xboole_0(esk9_0,k1_tarski(esk9_0)))|r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),X1)), inference(spm,[status(thm)],[c_0_86, c_0_146])).
% 10.07/10.25  cnf(c_0_159, negated_conjecture, (r2_hidden(esk8_0,X1)|r1_tarski(X2,esk1_2(esk7_1(k2_xboole_0(esk8_0,k1_tarski(esk8_0))),X1))|~r2_hidden(X2,esk1_2(esk7_1(k2_xboole_0(esk8_0,k1_tarski(esk8_0))),X1))), inference(spm,[status(thm)],[c_0_79, c_0_153])).
% 10.07/10.25  cnf(c_0_160, negated_conjecture, (esk7_1(X1)=k2_xboole_0(esk8_0,k1_tarski(esk8_0))|r2_hidden(esk7_1(X1),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),X1)), inference(spm,[status(thm)],[c_0_142, c_0_154])).
% 10.07/10.25  cnf(c_0_161, negated_conjecture, (r2_hidden(esk9_0,esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0))|r2_hidden(esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_155, c_0_133])).
% 10.07/10.25  cnf(c_0_162, negated_conjecture, (r2_hidden(esk2_3(esk8_0,esk8_0,esk9_0),esk8_0)|r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)), inference(spm,[status(thm)],[c_0_156, c_0_133])).
% 10.07/10.25  cnf(c_0_163, negated_conjecture, (r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)|r2_hidden(X1,esk2_3(esk8_0,esk8_0,X1))|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_122, c_0_151])).
% 10.07/10.25  cnf(c_0_164, negated_conjecture, (r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),X1)|r1_tarski(esk7_1(X1),k2_xboole_0(esk9_0,k1_tarski(esk9_0)))), inference(spm,[status(thm)],[c_0_157, c_0_158])).
% 10.07/10.25  cnf(c_0_165, negated_conjecture, (r2_hidden(esk8_0,X1)|r1_tarski(X2,esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),X1))|~r2_hidden(X2,esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_159, c_0_160]), c_0_61]), c_0_127])).
% 10.07/10.25  cnf(c_0_166, negated_conjecture, (r2_hidden(esk9_0,esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_161]), c_0_137])).
% 10.07/10.25  cnf(c_0_167, negated_conjecture, (r2_hidden(esk2_3(esk8_0,esk8_0,esk9_0),esk8_0)|r2_hidden(X1,k3_tarski(esk8_0))|~r2_hidden(X1,k2_xboole_0(esk9_0,k1_tarski(esk9_0)))), inference(spm,[status(thm)],[c_0_75, c_0_162])).
% 10.07/10.25  cnf(c_0_168, negated_conjecture, (r2_hidden(esk9_0,esk2_3(esk8_0,esk8_0,esk9_0))|r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)), inference(spm,[status(thm)],[c_0_163, c_0_133])).
% 10.07/10.25  cnf(c_0_169, negated_conjecture, (r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),X1)|r2_hidden(X2,k2_xboole_0(esk9_0,k1_tarski(esk9_0)))|~r2_hidden(X2,esk7_1(X1))), inference(spm,[status(thm)],[c_0_95, c_0_164])).
% 10.07/10.25  cnf(c_0_170, negated_conjecture, (r1_tarski(esk9_0,esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_165, c_0_166]), c_0_127])).
% 10.07/10.25  cnf(c_0_171, negated_conjecture, (r2_hidden(esk2_3(esk8_0,esk8_0,esk9_0),esk8_0)|r2_hidden(esk9_0,k3_tarski(esk8_0))), inference(spm,[status(thm)],[c_0_167, c_0_58])).
% 10.07/10.25  cnf(c_0_172, negated_conjecture, (r2_hidden(esk9_0,esk2_3(esk8_0,esk8_0,esk9_0))|r2_hidden(X1,k3_tarski(esk8_0))|~r2_hidden(X1,k2_xboole_0(esk9_0,k1_tarski(esk9_0)))), inference(spm,[status(thm)],[c_0_75, c_0_168])).
% 10.07/10.25  cnf(c_0_173, negated_conjecture, (r2_hidden(esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0),k2_xboole_0(esk9_0,k1_tarski(esk9_0)))|r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_169, c_0_124])).
% 10.07/10.25  cnf(c_0_174, negated_conjecture, (~r2_hidden(esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0),esk9_0)), inference(spm,[status(thm)],[c_0_47, c_0_170])).
% 10.07/10.25  cnf(c_0_175, negated_conjecture, (r2_hidden(esk9_0,k3_tarski(esk8_0))|r2_hidden(X1,k3_tarski(esk8_0))|~r2_hidden(X1,esk2_3(esk8_0,esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_75, c_0_171])).
% 10.07/10.25  cnf(c_0_176, negated_conjecture, (r2_hidden(esk9_0,esk2_3(esk8_0,esk8_0,esk9_0))|r2_hidden(esk9_0,k3_tarski(esk8_0))), inference(spm,[status(thm)],[c_0_172, c_0_58])).
% 10.07/10.25  cnf(c_0_177, negated_conjecture, (esk1_2(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk8_0)=esk9_0|r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_173]), c_0_174])).
% 10.07/10.25  cnf(c_0_178, negated_conjecture, (r2_hidden(esk9_0,k3_tarski(esk8_0))), inference(spm,[status(thm)],[c_0_175, c_0_176])).
% 10.07/10.25  cnf(c_0_179, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(esk9_0,k1_tarski(esk9_0)))), inference(spm,[status(thm)],[c_0_30, c_0_146])).
% 10.07/10.25  cnf(c_0_180, negated_conjecture, (r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_177]), c_0_133])]), c_0_137])).
% 10.07/10.25  cnf(c_0_181, negated_conjecture, (r2_hidden(esk2_3(esk8_0,k3_tarski(esk8_0),esk9_0),esk8_0)), inference(spm,[status(thm)],[c_0_111, c_0_178])).
% 10.07/10.25  cnf(c_0_182, negated_conjecture, (r1_ordinal1(X1,esk9_0)|~r2_hidden(X1,k2_xboole_0(esk9_0,k1_tarski(esk9_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_138]), c_0_179])).
% 10.07/10.25  cnf(c_0_183, negated_conjecture, (k2_xboole_0(esk9_0,k1_tarski(esk9_0))=esk8_0|r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)), inference(spm,[status(thm)],[c_0_142, c_0_180])).
% 10.07/10.25  cnf(c_0_184, negated_conjecture, (r1_tarski(X1,esk9_0)|~r1_ordinal1(X1,esk9_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_77, c_0_138])).
% 10.07/10.25  cnf(c_0_185, negated_conjecture, (v3_ordinal1(esk2_3(esk8_0,k3_tarski(esk8_0),esk9_0))), inference(spm,[status(thm)],[c_0_33, c_0_181])).
% 10.07/10.25  cnf(c_0_186, negated_conjecture, (r1_ordinal1(X1,esk9_0)|r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_182, c_0_183])).
% 10.07/10.25  cnf(c_0_187, negated_conjecture, (~r2_hidden(k1_ordinal1(esk9_0),esk8_0)|~v4_ordinal1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 10.07/10.25  cnf(c_0_188, plain, (r2_hidden(esk4_2(X1,X2),X1)|r2_hidden(esk3_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 10.07/10.25  cnf(c_0_189, negated_conjecture, (r1_tarski(esk2_3(esk8_0,k3_tarski(esk8_0),esk9_0),esk9_0)|~r1_ordinal1(esk2_3(esk8_0,k3_tarski(esk8_0),esk9_0),esk9_0)), inference(spm,[status(thm)],[c_0_184, c_0_185])).
% 10.07/10.25  cnf(c_0_190, negated_conjecture, (r1_ordinal1(esk2_3(esk8_0,k3_tarski(esk8_0),esk9_0),esk9_0)|r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)), inference(spm,[status(thm)],[c_0_186, c_0_181])).
% 10.07/10.25  cnf(c_0_191, negated_conjecture, (~v4_ordinal1(esk8_0)|~r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)), inference(rw,[status(thm)],[c_0_187, c_0_43])).
% 10.07/10.25  cnf(c_0_192, plain, (v4_ordinal1(X1)|r2_hidden(esk4_2(X1,X1),X1)|r2_hidden(esk3_2(X1,X1),X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_188])])).
% 10.07/10.25  cnf(c_0_193, negated_conjecture, (r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)|r1_tarski(esk2_3(esk8_0,k3_tarski(esk8_0),esk9_0),esk9_0)), inference(spm,[status(thm)],[c_0_189, c_0_190])).
% 10.07/10.25  cnf(c_0_194, negated_conjecture, (r2_hidden(esk9_0,esk2_3(esk8_0,k3_tarski(esk8_0),esk9_0))), inference(spm,[status(thm)],[c_0_122, c_0_178])).
% 10.07/10.25  cnf(c_0_195, negated_conjecture, (r2_hidden(esk3_2(esk8_0,esk8_0),esk8_0)|r2_hidden(esk4_2(esk8_0,esk8_0),esk8_0)|~r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)), inference(spm,[status(thm)],[c_0_191, c_0_192])).
% 10.07/10.25  cnf(c_0_196, negated_conjecture, (r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_193]), c_0_194])])).
% 10.07/10.25  cnf(c_0_197, plain, (r2_hidden(esk3_2(X1,X2),esk4_2(X1,X2))|r2_hidden(esk3_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 10.07/10.25  cnf(c_0_198, negated_conjecture, (r2_hidden(esk4_2(esk8_0,esk8_0),esk8_0)|r2_hidden(esk3_2(esk8_0,esk8_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_195, c_0_196])])).
% 10.07/10.25  cnf(c_0_199, plain, (v4_ordinal1(X1)|r2_hidden(esk3_2(X1,X1),esk4_2(X1,X1))|r2_hidden(esk3_2(X1,X1),X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_197])])).
% 10.07/10.25  cnf(c_0_200, negated_conjecture, (r2_hidden(esk8_0,k3_tarski(esk8_0))|r2_hidden(k3_tarski(esk8_0),esk8_0)|r2_hidden(esk6_1(esk8_0),esk8_0)|~r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)), inference(spm,[status(thm)],[c_0_191, c_0_32])).
% 10.07/10.25  cnf(c_0_201, negated_conjecture, (r2_hidden(esk3_2(esk8_0,esk8_0),esk8_0)|r1_tarski(esk4_2(esk8_0,esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_120, c_0_198])).
% 10.07/10.25  cnf(c_0_202, negated_conjecture, (r2_hidden(esk3_2(esk8_0,esk8_0),esk4_2(esk8_0,esk8_0))|r2_hidden(esk3_2(esk8_0,esk8_0),esk8_0)|~r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)), inference(spm,[status(thm)],[c_0_191, c_0_199])).
% 10.07/10.25  cnf(c_0_203, negated_conjecture, (r2_hidden(esk6_1(esk8_0),esk8_0)|r2_hidden(k3_tarski(esk8_0),esk8_0)|r2_hidden(esk8_0,k3_tarski(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_200, c_0_196])])).
% 10.07/10.25  cnf(c_0_204, negated_conjecture, (r2_hidden(esk3_2(esk8_0,esk8_0),esk8_0)|r2_hidden(X1,esk8_0)|~r2_hidden(X1,esk4_2(esk8_0,esk8_0))), inference(spm,[status(thm)],[c_0_95, c_0_201])).
% 10.07/10.25  cnf(c_0_205, negated_conjecture, (r2_hidden(esk3_2(esk8_0,esk8_0),esk4_2(esk8_0,esk8_0))|r2_hidden(esk3_2(esk8_0,esk8_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_202, c_0_196])])).
% 10.07/10.25  cnf(c_0_206, negated_conjecture, (v3_ordinal1(esk6_1(esk8_0))|r2_hidden(esk8_0,k3_tarski(esk8_0))|r2_hidden(k3_tarski(esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_33, c_0_203])).
% 10.07/10.25  cnf(c_0_207, negated_conjecture, (r2_hidden(esk3_2(esk8_0,esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_204, c_0_205])).
% 10.07/10.25  cnf(c_0_208, negated_conjecture, (~v4_ordinal1(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_191, c_0_196])])).
% 10.07/10.25  cnf(c_0_209, negated_conjecture, (v3_ordinal1(k3_tarski(esk8_0))|r2_hidden(esk8_0,k3_tarski(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_206]), c_0_33])).
% 10.07/10.25  cnf(c_0_210, plain, (X2=k3_tarski(X1)|~r2_hidden(esk3_2(X1,X2),X2)|~r2_hidden(esk3_2(X1,X2),X3)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 10.07/10.25  cnf(c_0_211, negated_conjecture, (r2_hidden(k2_xboole_0(esk3_2(esk8_0,esk8_0),k1_tarski(esk3_2(esk8_0,esk8_0))),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_207]), c_0_208])).
% 10.07/10.25  cnf(c_0_212, negated_conjecture, (k3_tarski(esk8_0)=esk8_0|r2_hidden(esk8_0,k3_tarski(esk8_0))|r2_hidden(k3_tarski(esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_25, c_0_209])).
% 10.07/10.25  cnf(c_0_213, negated_conjecture, (X1=k3_tarski(esk8_0)|~r2_hidden(esk3_2(esk8_0,X1),k2_xboole_0(esk3_2(esk8_0,esk8_0),k1_tarski(esk3_2(esk8_0,esk8_0))))|~r2_hidden(esk3_2(esk8_0,X1),X1)), inference(spm,[status(thm)],[c_0_210, c_0_211])).
% 10.07/10.25  cnf(c_0_214, negated_conjecture, (r2_hidden(k3_tarski(esk8_0),esk8_0)|r2_hidden(esk8_0,k3_tarski(esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_212]), c_0_208])).
% 10.07/10.25  cnf(c_0_215, negated_conjecture, (k3_tarski(esk8_0)=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_213, c_0_207]), c_0_58])])).
% 10.07/10.25  cnf(c_0_216, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_214, c_0_215]), c_0_215])]), c_0_127]), ['proof']).
% 10.07/10.25  # SZS output end CNFRefutation
% 10.07/10.25  # Proof object total steps             : 217
% 10.07/10.25  # Proof object clause steps            : 180
% 10.07/10.25  # Proof object formula steps           : 37
% 10.07/10.25  # Proof object conjectures             : 128
% 10.07/10.25  # Proof object clause conjectures      : 125
% 10.07/10.25  # Proof object formula conjectures     : 3
% 10.07/10.25  # Proof object initial clauses used    : 35
% 10.07/10.25  # Proof object initial formulas used   : 18
% 10.07/10.25  # Proof object generating inferences   : 127
% 10.07/10.25  # Proof object simplifying inferences  : 60
% 10.07/10.25  # Training examples: 0 positive, 0 negative
% 10.07/10.25  # Parsed axioms                        : 19
% 10.07/10.25  # Removed by relevancy pruning/SinE    : 0
% 10.07/10.25  # Initial clauses                      : 43
% 10.07/10.25  # Removed in clause preprocessing      : 1
% 10.07/10.25  # Initial clauses in saturation        : 42
% 10.07/10.25  # Processed clauses                    : 20318
% 10.07/10.25  # ...of these trivial                  : 524
% 10.07/10.25  # ...subsumed                          : 12137
% 10.07/10.25  # ...remaining for further processing  : 7657
% 10.07/10.25  # Other redundant clauses eliminated   : 44
% 10.07/10.25  # Clauses deleted for lack of memory   : 0
% 10.07/10.25  # Backward-subsumed                    : 982
% 10.07/10.25  # Backward-rewritten                   : 2064
% 10.07/10.25  # Generated clauses                    : 1013555
% 10.07/10.25  # ...of the previous two non-trivial   : 875422
% 10.07/10.25  # Contextual simplify-reflections      : 86
% 10.07/10.25  # Paramodulations                      : 1013455
% 10.07/10.25  # Factorizations                       : 4
% 10.07/10.25  # Equation resolutions                 : 44
% 10.07/10.25  # Propositional unsat checks           : 0
% 10.07/10.25  #    Propositional check models        : 0
% 10.07/10.25  #    Propositional check unsatisfiable : 0
% 10.07/10.25  #    Propositional clauses             : 0
% 10.07/10.25  #    Propositional clauses after purity: 0
% 10.07/10.25  #    Propositional unsat core size     : 0
% 10.07/10.25  #    Propositional preprocessing time  : 0.000
% 10.07/10.25  #    Propositional encoding time       : 0.000
% 10.07/10.25  #    Propositional solver time         : 0.000
% 10.07/10.25  #    Success case prop preproc time    : 0.000
% 10.07/10.25  #    Success case prop encoding time   : 0.000
% 10.07/10.25  #    Success case prop solver time     : 0.000
% 10.07/10.25  # Current number of processed clauses  : 4513
% 10.07/10.25  #    Positive orientable unit clauses  : 795
% 10.07/10.25  #    Positive unorientable unit clauses: 0
% 10.07/10.25  #    Negative unit clauses             : 159
% 10.07/10.25  #    Non-unit-clauses                  : 3559
% 10.07/10.25  # Current number of unprocessed clauses: 851536
% 10.07/10.25  # ...number of literals in the above   : 4510567
% 10.07/10.25  # Current number of archived formulas  : 0
% 10.07/10.25  # Current number of archived clauses   : 3139
% 10.07/10.25  # Clause-clause subsumption calls (NU) : 1875782
% 10.07/10.25  # Rec. Clause-clause subsumption calls : 669701
% 10.07/10.25  # Non-unit clause-clause subsumptions  : 9473
% 10.07/10.25  # Unit Clause-clause subsumption calls : 110642
% 10.07/10.25  # Rewrite failures with RHS unbound    : 0
% 10.07/10.25  # BW rewrite match attempts            : 2304
% 10.07/10.25  # BW rewrite match successes           : 132
% 10.07/10.25  # Condensation attempts                : 0
% 10.07/10.25  # Condensation successes               : 0
% 10.07/10.25  # Termbank termtop insertions          : 26860379
% 10.07/10.28  
% 10.07/10.28  # -------------------------------------------------
% 10.07/10.28  # User time                : 9.572 s
% 10.07/10.28  # System time              : 0.370 s
% 10.07/10.28  # Total time               : 9.942 s
% 10.07/10.28  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
