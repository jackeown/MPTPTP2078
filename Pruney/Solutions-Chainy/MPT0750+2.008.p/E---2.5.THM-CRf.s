%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:33 EST 2020

% Result     : Theorem 8.46s
% Output     : CNFRefutation 8.46s
% Verified   : 
% Statistics : Number of formulae       :  240 (298955 expanded)
%              Number of clauses        :  203 (133749 expanded)
%              Number of leaves         :   18 (70766 expanded)
%              Depth                    :   57
%              Number of atoms          :  605 (1174484 expanded)
%              Number of equality atoms :   48 (94413 expanded)
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

fof(t34_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,k1_ordinal1(X2))
          <=> r1_ordinal1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(t13_ordinal1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,k1_ordinal1(X2))
    <=> ( r2_hidden(X1,X2)
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(connectedness_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
        | r1_ordinal1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

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

fof(t14_ordinal1,axiom,(
    ! [X1] : X1 != k1_ordinal1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).

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
    ! [X36,X37] :
      ( ~ v3_ordinal1(X36)
      | ~ v3_ordinal1(X37)
      | r2_hidden(X36,X37)
      | X36 = X37
      | r2_hidden(X37,X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

fof(c_0_20,negated_conjecture,(
    ! [X50] :
      ( v3_ordinal1(esk7_0)
      & ( v3_ordinal1(esk8_0)
        | ~ v4_ordinal1(esk7_0) )
      & ( r2_hidden(esk8_0,esk7_0)
        | ~ v4_ordinal1(esk7_0) )
      & ( ~ r2_hidden(k1_ordinal1(esk8_0),esk7_0)
        | ~ v4_ordinal1(esk7_0) )
      & ( v4_ordinal1(esk7_0)
        | ~ v3_ordinal1(X50)
        | ~ r2_hidden(X50,esk7_0)
        | r2_hidden(k1_ordinal1(X50),esk7_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])])])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( v3_ordinal1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_23,plain,(
    ! [X41] :
      ( ( r2_hidden(esk5_1(X41),X41)
        | v3_ordinal1(k3_tarski(X41)) )
      & ( ~ v3_ordinal1(esk5_1(X41))
        | v3_ordinal1(k3_tarski(X41)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_ordinal1])])])])).

fof(c_0_24,plain,(
    ! [X27] :
      ( ( ~ v4_ordinal1(X27)
        | X27 = k3_tarski(X27) )
      & ( X27 != k3_tarski(X27)
        | v4_ordinal1(X27) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_ordinal1])])).

cnf(c_0_25,negated_conjecture,
    ( X1 = esk7_0
    | r2_hidden(X1,esk7_0)
    | r2_hidden(esk7_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( r2_hidden(esk5_1(X1),X1)
    | v3_ordinal1(k3_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X34,X35] :
      ( ~ v3_ordinal1(X35)
      | ~ r2_hidden(X34,X35)
      | v3_ordinal1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

cnf(c_0_28,plain,
    ( v4_ordinal1(X1)
    | X1 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( k3_tarski(X1) = esk7_0
    | r2_hidden(esk7_0,k3_tarski(X1))
    | r2_hidden(k3_tarski(X1),esk7_0)
    | r2_hidden(esk5_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0)
    | ~ v4_ordinal1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( v4_ordinal1(esk7_0)
    | r2_hidden(esk5_1(esk7_0),esk7_0)
    | r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29])])).

cnf(c_0_33,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk5_1(esk7_0),esk7_0)
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_35,plain,(
    ! [X38] :
      ( ~ v3_ordinal1(X38)
      | v3_ordinal1(k1_ordinal1(X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

fof(c_0_36,plain,(
    ! [X26] : k1_ordinal1(X26) = k2_xboole_0(X26,k1_tarski(X26)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

cnf(c_0_37,plain,
    ( v3_ordinal1(k3_tarski(X1))
    | ~ v3_ordinal1(esk5_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_38,negated_conjecture,
    ( v3_ordinal1(esk5_1(esk7_0))
    | r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_41,plain,(
    ! [X46,X47] :
      ( ~ r2_hidden(X46,X47)
      | ~ r1_tarski(X47,X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_42,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_43,negated_conjecture,
    ( v3_ordinal1(k3_tarski(esk7_0))
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_33])).

fof(c_0_44,plain,(
    ! [X39,X40] :
      ( ( ~ r2_hidden(X39,k1_ordinal1(X40))
        | r1_ordinal1(X39,X40)
        | ~ v3_ordinal1(X40)
        | ~ v3_ordinal1(X39) )
      & ( ~ r1_ordinal1(X39,X40)
        | r2_hidden(X39,k1_ordinal1(X40))
        | ~ v3_ordinal1(X40)
        | ~ v3_ordinal1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).

cnf(c_0_45,plain,
    ( v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_46,plain,(
    ! [X31,X32] :
      ( ( ~ r2_hidden(X31,k1_ordinal1(X32))
        | r2_hidden(X31,X32)
        | X31 = X32 )
      & ( ~ r2_hidden(X31,X32)
        | r2_hidden(X31,k1_ordinal1(X32)) )
      & ( X31 != X32
        | r2_hidden(X31,k1_ordinal1(X32)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).

cnf(c_0_47,negated_conjecture,
    ( v4_ordinal1(esk7_0)
    | r2_hidden(k1_ordinal1(X1),esk7_0)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( k3_tarski(esk7_0) = esk7_0
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_43])).

cnf(c_0_51,plain,
    ( r1_ordinal1(X1,X2)
    | ~ r2_hidden(X1,k1_ordinal1(X2))
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( v3_ordinal1(k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_22])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_54,plain,(
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

cnf(c_0_55,negated_conjecture,
    ( v4_ordinal1(esk7_0)
    | r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk7_0)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_40])).

cnf(c_0_56,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_50]),c_0_31])).

fof(c_0_58,plain,(
    ! [X28,X29] :
      ( ( ~ r1_ordinal1(X28,X29)
        | r1_tarski(X28,X29)
        | ~ v3_ordinal1(X28)
        | ~ v3_ordinal1(X29) )
      & ( ~ r1_tarski(X28,X29)
        | r1_ordinal1(X28,X29)
        | ~ v3_ordinal1(X28)
        | ~ v3_ordinal1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_59,plain,
    ( r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_51,c_0_40])).

cnf(c_0_60,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_52])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_53,c_0_40])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( v4_ordinal1(esk7_0)
    | r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(csr,[status(thm)],[c_0_55,c_0_33])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,k3_tarski(esk7_0)),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

fof(c_0_65,plain,(
    ! [X30] : r2_hidden(X30,k1_ordinal1(X30)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( r1_ordinal1(X1,esk7_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_22]),c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(k3_tarski(esk7_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_57])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk1_2(esk7_0,k3_tarski(esk7_0)),k1_tarski(esk1_2(esk7_0,k3_tarski(esk7_0)))),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_31])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

fof(c_0_72,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(X1,esk7_0)
    | ~ r1_ordinal1(X1,esk7_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_22])).

cnf(c_0_74,negated_conjecture,
    ( r1_ordinal1(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(X1,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk1_2(esk7_0,k3_tarski(esk7_0)),k1_tarski(esk1_2(esk7_0,k3_tarski(esk7_0))))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_71,c_0_40])).

cnf(c_0_77,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0)
    | r1_tarski(k3_tarski(esk7_0),esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_43]),c_0_74])).

cnf(c_0_79,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,k3_tarski(esk7_0)),k3_tarski(esk7_0))
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

fof(c_0_81,plain,(
    ! [X24,X25] :
      ( ~ v3_ordinal1(X24)
      | ~ v3_ordinal1(X25)
      | r1_ordinal1(X24,X25)
      | r1_ordinal1(X25,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).

cnf(c_0_82,negated_conjecture,
    ( k3_tarski(esk7_0) = esk7_0
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0)
    | ~ r1_tarski(esk7_0,k3_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0)
    | r1_tarski(esk7_0,k3_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

fof(c_0_84,plain,(
    ! [X43,X45] :
      ( v3_ordinal1(esk6_1(X43))
      & ~ r2_hidden(esk6_1(X43),X43)
      & ( ~ v3_ordinal1(X45)
        | r2_hidden(X45,X43)
        | r1_ordinal1(esk6_1(X43),X45) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_ordinal1])])])])])).

cnf(c_0_85,plain,
    ( r1_ordinal1(X1,X2)
    | r1_ordinal1(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_86,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_87,negated_conjecture,
    ( k3_tarski(esk7_0) = esk7_0
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_88,plain,
    ( v3_ordinal1(esk6_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( r1_ordinal1(X1,esk7_0)
    | r1_ordinal1(esk7_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_22])).

cnf(c_0_90,plain,
    ( r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_86])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_87]),c_0_31])).

cnf(c_0_92,plain,
    ( r1_tarski(X1,esk6_1(X2))
    | ~ r1_ordinal1(X1,esk6_1(X2))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_88])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(esk6_1(X1),esk7_0)
    | ~ r1_ordinal1(esk6_1(X1),esk7_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_88])).

cnf(c_0_94,negated_conjecture,
    ( r1_ordinal1(esk7_0,esk6_1(X1))
    | r1_ordinal1(esk6_1(X1),esk7_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_88])).

cnf(c_0_95,plain,
    ( ~ r2_hidden(esk6_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_96,negated_conjecture,
    ( esk6_1(X1) = esk7_0
    | r2_hidden(esk7_0,esk6_1(X1))
    | r2_hidden(esk6_1(X1),esk7_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_88])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_98,plain,
    ( r2_hidden(esk1_2(k2_xboole_0(X1,k1_tarski(X1)),X1),k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_76])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(esk7_0,esk6_1(X1))
    | ~ r1_ordinal1(esk7_0,esk6_1(X1)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_22])).

cnf(c_0_100,negated_conjecture,
    ( r1_ordinal1(esk7_0,esk6_1(X1))
    | r1_tarski(esk6_1(X1),esk7_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_101,negated_conjecture,
    ( r2_hidden(esk6_1(X1),esk7_0)
    | r2_hidden(esk7_0,esk6_1(X1))
    | ~ r2_hidden(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_97])).

cnf(c_0_103,plain,
    ( r2_hidden(X1,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k3_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_104,negated_conjecture,
    ( v3_ordinal1(esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_98])).

cnf(c_0_105,negated_conjecture,
    ( r1_tarski(esk6_1(X1),esk7_0)
    | r1_tarski(esk7_0,esk6_1(X1)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_106,negated_conjecture,
    ( r2_hidden(esk7_0,esk6_1(k2_xboole_0(esk7_0,k1_tarski(esk7_0))))
    | r2_hidden(esk6_1(k2_xboole_0(esk7_0,k1_tarski(esk7_0))),esk7_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_76])).

cnf(c_0_107,negated_conjecture,
    ( v3_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_97])).

cnf(c_0_108,negated_conjecture,
    ( r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_102])).

cnf(c_0_109,plain,
    ( r2_hidden(X1,esk2_3(X2,k3_tarski(X2),X1))
    | ~ r2_hidden(X1,k3_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_103])).

cnf(c_0_110,negated_conjecture,
    ( r1_tarski(X1,esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0))
    | ~ r1_ordinal1(X1,esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_104])).

cnf(c_0_111,plain,
    ( r2_hidden(X1,X2)
    | r1_ordinal1(esk6_1(X2),X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_112,negated_conjecture,
    ( r1_tarski(esk7_0,esk6_1(X1))
    | ~ r2_hidden(esk7_0,esk6_1(X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_105])).

cnf(c_0_113,negated_conjecture,
    ( r2_hidden(esk7_0,esk6_1(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_106]),c_0_95])).

cnf(c_0_114,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0)
    | r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_107]),c_0_108])).

cnf(c_0_115,negated_conjecture,
    ( r2_hidden(esk7_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_109,c_0_91])).

cnf(c_0_116,negated_conjecture,
    ( r1_tarski(esk6_1(X1),esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0))
    | ~ r1_ordinal1(esk6_1(X1),esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_110,c_0_88])).

cnf(c_0_117,negated_conjecture,
    ( r1_ordinal1(esk6_1(X1),esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0))
    | r2_hidden(esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_111,c_0_104])).

cnf(c_0_118,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_119,negated_conjecture,
    ( r1_tarski(esk7_0,esk6_1(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_120,negated_conjecture,
    ( r1_ordinal1(esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_98])).

cnf(c_0_121,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_122,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_123,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_114]),c_0_115])).

cnf(c_0_124,plain,
    ( r1_tarski(esk6_1(X1),esk6_1(X2))
    | ~ r1_ordinal1(esk6_1(X1),esk6_1(X2)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_88])).

cnf(c_0_125,plain,
    ( r1_ordinal1(esk6_1(X1),esk6_1(X2))
    | r2_hidden(esk6_1(X2),X1) ),
    inference(spm,[status(thm)],[c_0_111,c_0_88])).

cnf(c_0_126,negated_conjecture,
    ( r2_hidden(esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0),X1)
    | r1_tarski(esk6_1(X1),esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_127,negated_conjecture,
    ( r2_hidden(X1,esk6_1(k2_xboole_0(esk7_0,k1_tarski(esk7_0))))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_128,negated_conjecture,
    ( r2_hidden(esk7_0,esk6_1(esk6_1(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))))
    | r2_hidden(esk6_1(esk6_1(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))),esk7_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_113])).

cnf(c_0_129,negated_conjecture,
    ( r1_tarski(esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_104]),c_0_120])])).

cnf(c_0_130,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r1_ordinal1(X1,X2) ),
    inference(rw,[status(thm)],[c_0_121,c_0_40])).

cnf(c_0_131,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_122])).

cnf(c_0_132,negated_conjecture,
    ( r2_hidden(esk8_0,k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_123])).

cnf(c_0_133,plain,
    ( r2_hidden(esk6_1(X1),X2)
    | r1_tarski(esk6_1(X2),esk6_1(X1)) ),
    inference(spm,[status(thm)],[c_0_124,c_0_125])).

cnf(c_0_134,negated_conjecture,
    ( r2_hidden(esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0),X1)
    | r2_hidden(X2,esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0))
    | ~ r2_hidden(X2,esk6_1(X1)) ),
    inference(spm,[status(thm)],[c_0_118,c_0_126])).

cnf(c_0_135,negated_conjecture,
    ( r2_hidden(esk7_0,esk6_1(esk6_1(k2_xboole_0(esk7_0,k1_tarski(esk7_0))))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_95])).

cnf(c_0_136,negated_conjecture,
    ( ~ r2_hidden(esk7_0,esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_129])).

cnf(c_0_137,negated_conjecture,
    ( r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))
    | ~ r1_ordinal1(X1,esk7_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_130,c_0_22])).

cnf(c_0_138,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_131])).

cnf(c_0_139,negated_conjecture,
    ( v3_ordinal1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_123])).

cnf(c_0_140,negated_conjecture,
    ( r1_ordinal1(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_132])).

cnf(c_0_141,plain,
    ( r2_hidden(esk6_1(X1),X2)
    | r2_hidden(X3,esk6_1(X1))
    | ~ r2_hidden(X3,esk6_1(X2)) ),
    inference(spm,[status(thm)],[c_0_118,c_0_133])).

cnf(c_0_142,negated_conjecture,
    ( r2_hidden(esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0),esk6_1(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_135]),c_0_136])).

cnf(c_0_143,negated_conjecture,
    ( ~ r1_ordinal1(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_52]),c_0_138])).

fof(c_0_144,plain,(
    ! [X33] : X33 != k1_ordinal1(X33) ),
    inference(variable_rename,[status(thm)],[t14_ordinal1])).

cnf(c_0_145,negated_conjecture,
    ( r1_tarski(esk8_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_139]),c_0_140])])).

cnf(c_0_146,negated_conjecture,
    ( r2_hidden(esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0),esk6_1(X1))
    | r2_hidden(esk6_1(X1),k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_141,c_0_142])).

cnf(c_0_147,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))
    | ~ r1_ordinal1(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_52])).

cnf(c_0_148,negated_conjecture,
    ( r1_ordinal1(esk7_0,k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_52]),c_0_143])).

cnf(c_0_149,plain,
    ( X1 != k1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_144])).

cnf(c_0_150,negated_conjecture,
    ( v3_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_139])).

cnf(c_0_151,negated_conjecture,
    ( r1_tarski(X1,esk8_0)
    | ~ r1_ordinal1(X1,esk8_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_139])).

cnf(c_0_152,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_118,c_0_145])).

cnf(c_0_153,negated_conjecture,
    ( r2_hidden(esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0),X1)
    | r2_hidden(esk6_1(X1),k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_146]),c_0_138])).

cnf(c_0_154,negated_conjecture,
    ( r1_tarski(esk7_0,k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_22]),c_0_148])])).

cnf(c_0_155,plain,
    ( X1 != k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(rw,[status(thm)],[c_0_149,c_0_40])).

cnf(c_0_156,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | ~ r1_ordinal1(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_150])).

cnf(c_0_157,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))
    | ~ r1_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_137,c_0_150])).

cnf(c_0_158,negated_conjecture,
    ( r1_ordinal1(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | r1_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_150])).

cnf(c_0_159,negated_conjecture,
    ( r1_tarski(esk6_1(X1),esk8_0)
    | ~ r1_ordinal1(esk6_1(X1),esk8_0) ),
    inference(spm,[status(thm)],[c_0_151,c_0_88])).

cnf(c_0_160,negated_conjecture,
    ( r1_ordinal1(esk6_1(X1),esk8_0)
    | r2_hidden(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_111,c_0_139])).

cnf(c_0_161,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | ~ r2_hidden(X1,k1_ordinal1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_162,negated_conjecture,
    ( r2_hidden(esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0),esk7_0)
    | r2_hidden(esk6_1(esk8_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_152,c_0_153])).

cnf(c_0_163,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_154]),c_0_155])).

cnf(c_0_164,negated_conjecture,
    ( r1_tarski(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | ~ r1_ordinal1(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_156,c_0_22])).

cnf(c_0_165,negated_conjecture,
    ( r1_ordinal1(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_157,c_0_158])).

cnf(c_0_166,negated_conjecture,
    ( r2_hidden(esk8_0,X1)
    | r1_tarski(esk6_1(X1),esk8_0) ),
    inference(spm,[status(thm)],[c_0_159,c_0_160])).

cnf(c_0_167,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_161,c_0_40])).

cnf(c_0_168,negated_conjecture,
    ( r2_hidden(esk6_1(esk8_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_162]),c_0_163])).

cnf(c_0_169,negated_conjecture,
    ( r2_hidden(esk6_1(esk7_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_153]),c_0_163])).

cnf(c_0_170,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))
    | r1_tarski(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_165])).

cnf(c_0_171,negated_conjecture,
    ( r2_hidden(esk8_0,X1)
    | ~ r2_hidden(esk8_0,esk6_1(X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_166])).

cnf(c_0_172,negated_conjecture,
    ( esk6_1(esk8_0) = esk7_0
    | r2_hidden(esk6_1(esk8_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_167,c_0_168])).

cnf(c_0_173,negated_conjecture,
    ( esk6_1(esk7_0) = esk7_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_167,c_0_169]),c_0_95])).

cnf(c_0_174,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))
    | r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_118,c_0_170])).

cnf(c_0_175,negated_conjecture,
    ( r2_hidden(esk6_1(esk8_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_172]),c_0_123])]),c_0_138])).

cnf(c_0_176,plain,
    ( X1 = k3_tarski(X1)
    | ~ v4_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_177,negated_conjecture,
    ( v4_ordinal1(esk7_0)
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_123])).

cnf(c_0_178,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_150])).

cnf(c_0_179,negated_conjecture,
    ( r2_hidden(esk6_1(X1),esk7_0)
    | r2_hidden(X2,esk6_1(X1))
    | ~ r2_hidden(X2,esk7_0) ),
    inference(spm,[status(thm)],[c_0_141,c_0_173])).

cnf(c_0_180,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))
    | r2_hidden(esk6_1(esk8_0),k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_174,c_0_175])).

cnf(c_0_181,negated_conjecture,
    ( k3_tarski(esk7_0) = esk7_0
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_176,c_0_177])).

cnf(c_0_182,negated_conjecture,
    ( r1_ordinal1(X1,esk8_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_139]),c_0_178])).

cnf(c_0_183,negated_conjecture,
    ( k2_xboole_0(esk8_0,k1_tarski(esk8_0)) = esk7_0
    | r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_150])).

cnf(c_0_184,plain,
    ( r2_hidden(esk6_1(X1),X2)
    | ~ r2_hidden(esk6_1(X1),esk6_1(X2)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_133])).

cnf(c_0_185,negated_conjecture,
    ( r2_hidden(esk6_1(esk8_0),esk6_1(X1))
    | r2_hidden(esk6_1(X1),esk7_0) ),
    inference(spm,[status(thm)],[c_0_179,c_0_175])).

cnf(c_0_186,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | ~ r1_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_150])).

cnf(c_0_187,negated_conjecture,
    ( r1_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | r2_hidden(esk6_1(esk8_0),k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_180])).

cnf(c_0_188,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | r2_hidden(esk2_3(esk7_0,esk7_0,X1),esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_181])).

cnf(c_0_189,negated_conjecture,
    ( r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | ~ r1_ordinal1(X1,esk8_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_130,c_0_139])).

cnf(c_0_190,negated_conjecture,
    ( r1_ordinal1(X1,esk8_0)
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_182,c_0_183])).

cnf(c_0_191,negated_conjecture,
    ( r2_hidden(esk6_1(X1),esk7_0)
    | r2_hidden(esk6_1(esk8_0),X1) ),
    inference(spm,[status(thm)],[c_0_184,c_0_185])).

cnf(c_0_192,negated_conjecture,
    ( r2_hidden(esk6_1(esk8_0),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | r1_tarski(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_186,c_0_187])).

cnf(c_0_193,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,esk7_0,esk8_0),esk7_0)
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_188,c_0_123])).

cnf(c_0_194,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | r2_hidden(X1,esk2_3(esk7_0,esk7_0,X1))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_109,c_0_181])).

cnf(c_0_195,plain,
    ( v3_ordinal1(k2_xboole_0(esk6_1(X1),k1_tarski(esk6_1(X1)))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_88])).

cnf(c_0_196,negated_conjecture,
    ( r2_hidden(esk6_1(X1),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | ~ r1_ordinal1(esk6_1(X1),esk8_0) ),
    inference(spm,[status(thm)],[c_0_189,c_0_88])).

cnf(c_0_197,negated_conjecture,
    ( r1_ordinal1(esk6_1(esk8_0),esk8_0)
    | r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_190,c_0_191]),c_0_173]),c_0_138])).

cnf(c_0_198,negated_conjecture,
    ( r2_hidden(esk6_1(esk8_0),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | ~ r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_192])).

cnf(c_0_199,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,esk7_0,esk8_0),esk7_0)
    | r2_hidden(X1,k3_tarski(esk7_0))
    | ~ r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_193])).

cnf(c_0_200,negated_conjecture,
    ( r2_hidden(esk8_0,esk2_3(esk7_0,esk7_0,esk8_0))
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_194,c_0_123])).

cnf(c_0_201,plain,
    ( r1_ordinal1(esk6_1(X1),k2_xboole_0(esk6_1(X2),k1_tarski(esk6_1(X2))))
    | r2_hidden(k2_xboole_0(esk6_1(X2),k1_tarski(esk6_1(X2))),X1) ),
    inference(spm,[status(thm)],[c_0_111,c_0_195])).

cnf(c_0_202,negated_conjecture,
    ( r2_hidden(esk6_1(esk8_0),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_196,c_0_197]),c_0_198])).

cnf(c_0_203,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,esk7_0,esk8_0),esk7_0)
    | r2_hidden(esk8_0,k3_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_199,c_0_76])).

cnf(c_0_204,negated_conjecture,
    ( r2_hidden(esk8_0,esk2_3(esk7_0,esk7_0,esk8_0))
    | r2_hidden(X1,k3_tarski(esk7_0))
    | ~ r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_200])).

cnf(c_0_205,negated_conjecture,
    ( r1_ordinal1(esk7_0,k2_xboole_0(esk6_1(X1),k1_tarski(esk6_1(X1))))
    | r2_hidden(k2_xboole_0(esk6_1(X1),k1_tarski(esk6_1(X1))),esk7_0) ),
    inference(spm,[status(thm)],[c_0_201,c_0_173])).

cnf(c_0_206,negated_conjecture,
    ( esk6_1(esk8_0) = esk8_0
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_167,c_0_202]),c_0_95])).

cnf(c_0_207,negated_conjecture,
    ( r2_hidden(esk8_0,k3_tarski(esk7_0))
    | r2_hidden(X1,k3_tarski(esk7_0))
    | ~ r2_hidden(X1,esk2_3(esk7_0,esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_203])).

cnf(c_0_208,negated_conjecture,
    ( r2_hidden(esk8_0,esk2_3(esk7_0,esk7_0,esk8_0))
    | r2_hidden(esk8_0,k3_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_204,c_0_76])).

cnf(c_0_209,negated_conjecture,
    ( r1_ordinal1(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_205,c_0_206])).

cnf(c_0_210,negated_conjecture,
    ( r2_hidden(esk8_0,k3_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_207,c_0_208])).

cnf(c_0_211,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | r1_tarski(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_209])).

cnf(c_0_212,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_210])).

cnf(c_0_213,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_118,c_0_211])).

cnf(c_0_214,negated_conjecture,
    ( v3_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_212])).

cnf(c_0_215,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_213,c_0_212])).

cnf(c_0_216,negated_conjecture,
    ( ~ r2_hidden(k1_ordinal1(esk8_0),esk7_0)
    | ~ v4_ordinal1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_217,negated_conjecture,
    ( r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)
    | ~ r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_151,c_0_214])).

cnf(c_0_218,negated_conjecture,
    ( r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_182,c_0_215])).

cnf(c_0_219,negated_conjecture,
    ( ~ v4_ordinal1(esk7_0)
    | ~ r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(rw,[status(thm)],[c_0_216,c_0_40])).

cnf(c_0_220,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_217,c_0_218])).

cnf(c_0_221,negated_conjecture,
    ( r2_hidden(esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_210])).

cnf(c_0_222,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk5_1(esk7_0),esk7_0)
    | ~ r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_219,c_0_32])).

cnf(c_0_223,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_220]),c_0_221])])).

cnf(c_0_224,negated_conjecture,
    ( r2_hidden(esk5_1(esk7_0),esk7_0)
    | r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_222,c_0_223])])).

cnf(c_0_225,negated_conjecture,
    ( v3_ordinal1(esk5_1(esk7_0))
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(k3_tarski(esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_224])).

cnf(c_0_226,negated_conjecture,
    ( v3_ordinal1(k3_tarski(esk7_0))
    | r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_225]),c_0_33])).

cnf(c_0_227,negated_conjecture,
    ( k3_tarski(esk7_0) = esk7_0
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(k3_tarski(esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_226])).

cnf(c_0_228,negated_conjecture,
    ( ~ v4_ordinal1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_219,c_0_223])])).

cnf(c_0_229,negated_conjecture,
    ( r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_227]),c_0_228])).

cnf(c_0_230,negated_conjecture,
    ( r2_hidden(k2_xboole_0(k3_tarski(esk7_0),k1_tarski(k3_tarski(esk7_0))),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_229]),c_0_228])).

cnf(c_0_231,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(X1,k3_tarski(esk7_0))
    | ~ r2_hidden(X1,k2_xboole_0(k3_tarski(esk7_0),k1_tarski(k3_tarski(esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_230])).

cnf(c_0_232,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_231,c_0_76]),c_0_138])).

cnf(c_0_233,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_232])).

cnf(c_0_234,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_233])).

cnf(c_0_235,negated_conjecture,
    ( v3_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_233])).

cnf(c_0_236,negated_conjecture,
    ( r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_234])).

cnf(c_0_237,negated_conjecture,
    ( r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_235]),c_0_236])])).

cnf(c_0_238,negated_conjecture,
    ( r2_hidden(esk7_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_232])).

cnf(c_0_239,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_237]),c_0_238])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:25:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 8.46/8.69  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 8.46/8.69  # and selection function SelectCQIArEqFirst.
% 8.46/8.69  #
% 8.46/8.69  # Preprocessing time       : 0.029 s
% 8.46/8.69  # Presaturation interreduction done
% 8.46/8.69  
% 8.46/8.69  # Proof found!
% 8.46/8.69  # SZS status Theorem
% 8.46/8.69  # SZS output start CNFRefutation
% 8.46/8.69  fof(t41_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_ordinal1)).
% 8.46/8.69  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 8.46/8.69  fof(t35_ordinal1, axiom, ![X1]:(![X2]:(r2_hidden(X2,X1)=>v3_ordinal1(X2))=>v3_ordinal1(k3_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_ordinal1)).
% 8.46/8.69  fof(d6_ordinal1, axiom, ![X1]:(v4_ordinal1(X1)<=>X1=k3_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_ordinal1)).
% 8.46/8.69  fof(t23_ordinal1, axiom, ![X1, X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>v3_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_ordinal1)).
% 8.46/8.69  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 8.46/8.69  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 8.46/8.69  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 8.46/8.69  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.46/8.69  fof(t34_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 8.46/8.69  fof(t13_ordinal1, axiom, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 8.46/8.69  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 8.46/8.69  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 8.46/8.69  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 8.46/8.69  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.46/8.69  fof(connectedness_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 8.46/8.69  fof(t39_ordinal1, axiom, ![X1]:?[X2]:((v3_ordinal1(X2)&~(r2_hidden(X2,X1)))&![X3]:(v3_ordinal1(X3)=>(~(r2_hidden(X3,X1))=>r1_ordinal1(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_ordinal1)).
% 8.46/8.69  fof(t14_ordinal1, axiom, ![X1]:X1!=k1_ordinal1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_ordinal1)).
% 8.46/8.69  fof(c_0_18, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1)))))), inference(assume_negation,[status(cth)],[t41_ordinal1])).
% 8.46/8.69  fof(c_0_19, plain, ![X36, X37]:(~v3_ordinal1(X36)|(~v3_ordinal1(X37)|(r2_hidden(X36,X37)|X36=X37|r2_hidden(X37,X36)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 8.46/8.69  fof(c_0_20, negated_conjecture, ![X50]:(v3_ordinal1(esk7_0)&(((v3_ordinal1(esk8_0)|~v4_ordinal1(esk7_0))&((r2_hidden(esk8_0,esk7_0)|~v4_ordinal1(esk7_0))&(~r2_hidden(k1_ordinal1(esk8_0),esk7_0)|~v4_ordinal1(esk7_0))))&(v4_ordinal1(esk7_0)|(~v3_ordinal1(X50)|(~r2_hidden(X50,esk7_0)|r2_hidden(k1_ordinal1(X50),esk7_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])])])).
% 8.46/8.69  cnf(c_0_21, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 8.46/8.69  cnf(c_0_22, negated_conjecture, (v3_ordinal1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 8.46/8.69  fof(c_0_23, plain, ![X41]:((r2_hidden(esk5_1(X41),X41)|v3_ordinal1(k3_tarski(X41)))&(~v3_ordinal1(esk5_1(X41))|v3_ordinal1(k3_tarski(X41)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_ordinal1])])])])).
% 8.46/8.69  fof(c_0_24, plain, ![X27]:((~v4_ordinal1(X27)|X27=k3_tarski(X27))&(X27!=k3_tarski(X27)|v4_ordinal1(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_ordinal1])])).
% 8.46/8.69  cnf(c_0_25, negated_conjecture, (X1=esk7_0|r2_hidden(X1,esk7_0)|r2_hidden(esk7_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 8.46/8.69  cnf(c_0_26, plain, (r2_hidden(esk5_1(X1),X1)|v3_ordinal1(k3_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 8.46/8.69  fof(c_0_27, plain, ![X34, X35]:(~v3_ordinal1(X35)|(~r2_hidden(X34,X35)|v3_ordinal1(X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).
% 8.46/8.69  cnf(c_0_28, plain, (v4_ordinal1(X1)|X1!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 8.46/8.69  cnf(c_0_29, negated_conjecture, (k3_tarski(X1)=esk7_0|r2_hidden(esk7_0,k3_tarski(X1))|r2_hidden(k3_tarski(X1),esk7_0)|r2_hidden(esk5_1(X1),X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 8.46/8.69  cnf(c_0_30, plain, (v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 8.46/8.69  cnf(c_0_31, negated_conjecture, (r2_hidden(esk8_0,esk7_0)|~v4_ordinal1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 8.46/8.69  cnf(c_0_32, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(esk5_1(esk7_0),esk7_0)|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29])])).
% 8.46/8.69  cnf(c_0_33, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_30, c_0_22])).
% 8.46/8.69  cnf(c_0_34, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk5_1(esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 8.46/8.69  fof(c_0_35, plain, ![X38]:(~v3_ordinal1(X38)|v3_ordinal1(k1_ordinal1(X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 8.46/8.69  fof(c_0_36, plain, ![X26]:k1_ordinal1(X26)=k2_xboole_0(X26,k1_tarski(X26)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 8.46/8.69  cnf(c_0_37, plain, (v3_ordinal1(k3_tarski(X1))|~v3_ordinal1(esk5_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 8.46/8.69  cnf(c_0_38, negated_conjecture, (v3_ordinal1(esk5_1(esk7_0))|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 8.46/8.69  cnf(c_0_39, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 8.46/8.69  cnf(c_0_40, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 8.46/8.69  fof(c_0_41, plain, ![X46, X47]:(~r2_hidden(X46,X47)|~r1_tarski(X47,X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 8.46/8.69  fof(c_0_42, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 8.46/8.69  cnf(c_0_43, negated_conjecture, (v3_ordinal1(k3_tarski(esk7_0))|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_33])).
% 8.46/8.69  fof(c_0_44, plain, ![X39, X40]:((~r2_hidden(X39,k1_ordinal1(X40))|r1_ordinal1(X39,X40)|~v3_ordinal1(X40)|~v3_ordinal1(X39))&(~r1_ordinal1(X39,X40)|r2_hidden(X39,k1_ordinal1(X40))|~v3_ordinal1(X40)|~v3_ordinal1(X39))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).
% 8.46/8.69  cnf(c_0_45, plain, (v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 8.46/8.69  fof(c_0_46, plain, ![X31, X32]:((~r2_hidden(X31,k1_ordinal1(X32))|(r2_hidden(X31,X32)|X31=X32))&((~r2_hidden(X31,X32)|r2_hidden(X31,k1_ordinal1(X32)))&(X31!=X32|r2_hidden(X31,k1_ordinal1(X32))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).
% 8.46/8.69  cnf(c_0_47, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(k1_ordinal1(X1),esk7_0)|~v3_ordinal1(X1)|~r2_hidden(X1,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 8.46/8.69  cnf(c_0_48, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 8.46/8.69  cnf(c_0_49, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 8.46/8.69  cnf(c_0_50, negated_conjecture, (k3_tarski(esk7_0)=esk7_0|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_25, c_0_43])).
% 8.46/8.69  cnf(c_0_51, plain, (r1_ordinal1(X1,X2)|~r2_hidden(X1,k1_ordinal1(X2))|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 8.46/8.69  cnf(c_0_52, negated_conjecture, (v3_ordinal1(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(spm,[status(thm)],[c_0_45, c_0_22])).
% 8.46/8.69  cnf(c_0_53, plain, (r2_hidden(X1,k1_ordinal1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 8.46/8.69  fof(c_0_54, plain, ![X13, X14, X15, X17, X18, X19, X20, X22]:((((r2_hidden(X15,esk2_3(X13,X14,X15))|~r2_hidden(X15,X14)|X14!=k3_tarski(X13))&(r2_hidden(esk2_3(X13,X14,X15),X13)|~r2_hidden(X15,X14)|X14!=k3_tarski(X13)))&(~r2_hidden(X17,X18)|~r2_hidden(X18,X13)|r2_hidden(X17,X14)|X14!=k3_tarski(X13)))&((~r2_hidden(esk3_2(X19,X20),X20)|(~r2_hidden(esk3_2(X19,X20),X22)|~r2_hidden(X22,X19))|X20=k3_tarski(X19))&((r2_hidden(esk3_2(X19,X20),esk4_2(X19,X20))|r2_hidden(esk3_2(X19,X20),X20)|X20=k3_tarski(X19))&(r2_hidden(esk4_2(X19,X20),X19)|r2_hidden(esk3_2(X19,X20),X20)|X20=k3_tarski(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 8.46/8.69  cnf(c_0_55, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk7_0)|~v3_ordinal1(X1)|~r2_hidden(X1,esk7_0)), inference(rw,[status(thm)],[c_0_47, c_0_40])).
% 8.46/8.69  cnf(c_0_56, plain, (r2_hidden(esk1_2(X1,X2),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 8.46/8.69  cnf(c_0_57, negated_conjecture, (r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_50]), c_0_31])).
% 8.46/8.69  fof(c_0_58, plain, ![X28, X29]:((~r1_ordinal1(X28,X29)|r1_tarski(X28,X29)|(~v3_ordinal1(X28)|~v3_ordinal1(X29)))&(~r1_tarski(X28,X29)|r1_ordinal1(X28,X29)|(~v3_ordinal1(X28)|~v3_ordinal1(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 8.46/8.69  cnf(c_0_59, plain, (r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_51, c_0_40])).
% 8.46/8.69  cnf(c_0_60, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(spm,[status(thm)],[c_0_30, c_0_52])).
% 8.46/8.69  cnf(c_0_61, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_53, c_0_40])).
% 8.46/8.69  cnf(c_0_62, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 8.46/8.69  cnf(c_0_63, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk7_0)|~r2_hidden(X1,esk7_0)), inference(csr,[status(thm)],[c_0_55, c_0_33])).
% 8.46/8.69  cnf(c_0_64, negated_conjecture, (r2_hidden(esk1_2(esk7_0,k3_tarski(esk7_0)),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 8.46/8.69  fof(c_0_65, plain, ![X30]:r2_hidden(X30,k1_ordinal1(X30)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 8.46/8.69  cnf(c_0_66, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 8.46/8.69  cnf(c_0_67, negated_conjecture, (r1_ordinal1(X1,esk7_0)|~r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_22]), c_0_60])).
% 8.46/8.69  cnf(c_0_68, negated_conjecture, (r2_hidden(k3_tarski(esk7_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_61, c_0_57])).
% 8.46/8.69  cnf(c_0_69, plain, (r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X3,X2)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_62])).
% 8.46/8.69  cnf(c_0_70, negated_conjecture, (r2_hidden(k2_xboole_0(esk1_2(esk7_0,k3_tarski(esk7_0)),k1_tarski(esk1_2(esk7_0,k3_tarski(esk7_0)))),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_31])).
% 8.46/8.69  cnf(c_0_71, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 8.46/8.69  fof(c_0_72, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 8.46/8.69  cnf(c_0_73, negated_conjecture, (r1_tarski(X1,esk7_0)|~r1_ordinal1(X1,esk7_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_66, c_0_22])).
% 8.46/8.69  cnf(c_0_74, negated_conjecture, (r1_ordinal1(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 8.46/8.69  cnf(c_0_75, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(X1,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)|~r2_hidden(X1,k2_xboole_0(esk1_2(esk7_0,k3_tarski(esk7_0)),k1_tarski(esk1_2(esk7_0,k3_tarski(esk7_0)))))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 8.46/8.69  cnf(c_0_76, plain, (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_71, c_0_40])).
% 8.46/8.69  cnf(c_0_77, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 8.46/8.69  cnf(c_0_78, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)|r1_tarski(k3_tarski(esk7_0),esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_43]), c_0_74])).
% 8.46/8.69  cnf(c_0_79, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 8.46/8.69  cnf(c_0_80, negated_conjecture, (r2_hidden(esk1_2(esk7_0,k3_tarski(esk7_0)),k3_tarski(esk7_0))|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 8.46/8.69  fof(c_0_81, plain, ![X24, X25]:(~v3_ordinal1(X24)|~v3_ordinal1(X25)|(r1_ordinal1(X24,X25)|r1_ordinal1(X25,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).
% 8.46/8.69  cnf(c_0_82, negated_conjecture, (k3_tarski(esk7_0)=esk7_0|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)|~r1_tarski(esk7_0,k3_tarski(esk7_0))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 8.46/8.69  cnf(c_0_83, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)|r1_tarski(esk7_0,k3_tarski(esk7_0))), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 8.46/8.69  fof(c_0_84, plain, ![X43, X45]:((v3_ordinal1(esk6_1(X43))&~r2_hidden(esk6_1(X43),X43))&(~v3_ordinal1(X45)|(r2_hidden(X45,X43)|r1_ordinal1(esk6_1(X43),X45)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_ordinal1])])])])])).
% 8.46/8.69  cnf(c_0_85, plain, (r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 8.46/8.69  cnf(c_0_86, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|X2!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 8.46/8.69  cnf(c_0_87, negated_conjecture, (k3_tarski(esk7_0)=esk7_0|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 8.46/8.69  cnf(c_0_88, plain, (v3_ordinal1(esk6_1(X1))), inference(split_conjunct,[status(thm)],[c_0_84])).
% 8.46/8.69  cnf(c_0_89, negated_conjecture, (r1_ordinal1(X1,esk7_0)|r1_ordinal1(esk7_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_85, c_0_22])).
% 8.46/8.69  cnf(c_0_90, plain, (r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)|~r2_hidden(X2,k3_tarski(X1))), inference(er,[status(thm)],[c_0_86])).
% 8.46/8.69  cnf(c_0_91, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_87]), c_0_31])).
% 8.46/8.69  cnf(c_0_92, plain, (r1_tarski(X1,esk6_1(X2))|~r1_ordinal1(X1,esk6_1(X2))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_66, c_0_88])).
% 8.46/8.69  cnf(c_0_93, negated_conjecture, (r1_tarski(esk6_1(X1),esk7_0)|~r1_ordinal1(esk6_1(X1),esk7_0)), inference(spm,[status(thm)],[c_0_73, c_0_88])).
% 8.46/8.69  cnf(c_0_94, negated_conjecture, (r1_ordinal1(esk7_0,esk6_1(X1))|r1_ordinal1(esk6_1(X1),esk7_0)), inference(spm,[status(thm)],[c_0_89, c_0_88])).
% 8.46/8.69  cnf(c_0_95, plain, (~r2_hidden(esk6_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 8.46/8.69  cnf(c_0_96, negated_conjecture, (esk6_1(X1)=esk7_0|r2_hidden(esk7_0,esk6_1(X1))|r2_hidden(esk6_1(X1),esk7_0)), inference(spm,[status(thm)],[c_0_25, c_0_88])).
% 8.46/8.69  cnf(c_0_97, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 8.46/8.69  cnf(c_0_98, plain, (r2_hidden(esk1_2(k2_xboole_0(X1,k1_tarski(X1)),X1),k2_xboole_0(X1,k1_tarski(X1)))), inference(spm,[status(thm)],[c_0_56, c_0_76])).
% 8.46/8.69  cnf(c_0_99, negated_conjecture, (r1_tarski(esk7_0,esk6_1(X1))|~r1_ordinal1(esk7_0,esk6_1(X1))), inference(spm,[status(thm)],[c_0_92, c_0_22])).
% 8.46/8.69  cnf(c_0_100, negated_conjecture, (r1_ordinal1(esk7_0,esk6_1(X1))|r1_tarski(esk6_1(X1),esk7_0)), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 8.46/8.69  cnf(c_0_101, negated_conjecture, (r2_hidden(esk6_1(X1),esk7_0)|r2_hidden(esk7_0,esk6_1(X1))|~r2_hidden(esk7_0,X1)), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 8.46/8.69  cnf(c_0_102, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_61, c_0_97])).
% 8.46/8.69  cnf(c_0_103, plain, (r2_hidden(X1,esk2_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k3_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 8.46/8.69  cnf(c_0_104, negated_conjecture, (v3_ordinal1(esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0))), inference(spm,[status(thm)],[c_0_60, c_0_98])).
% 8.46/8.69  cnf(c_0_105, negated_conjecture, (r1_tarski(esk6_1(X1),esk7_0)|r1_tarski(esk7_0,esk6_1(X1))), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 8.46/8.69  cnf(c_0_106, negated_conjecture, (r2_hidden(esk7_0,esk6_1(k2_xboole_0(esk7_0,k1_tarski(esk7_0))))|r2_hidden(esk6_1(k2_xboole_0(esk7_0,k1_tarski(esk7_0))),esk7_0)), inference(spm,[status(thm)],[c_0_101, c_0_76])).
% 8.46/8.69  cnf(c_0_107, negated_conjecture, (v3_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_33, c_0_97])).
% 8.46/8.69  cnf(c_0_108, negated_conjecture, (r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_67, c_0_102])).
% 8.46/8.69  cnf(c_0_109, plain, (r2_hidden(X1,esk2_3(X2,k3_tarski(X2),X1))|~r2_hidden(X1,k3_tarski(X2))), inference(er,[status(thm)],[c_0_103])).
% 8.46/8.69  cnf(c_0_110, negated_conjecture, (r1_tarski(X1,esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0))|~r1_ordinal1(X1,esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_66, c_0_104])).
% 8.46/8.69  cnf(c_0_111, plain, (r2_hidden(X1,X2)|r1_ordinal1(esk6_1(X2),X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 8.46/8.69  cnf(c_0_112, negated_conjecture, (r1_tarski(esk7_0,esk6_1(X1))|~r2_hidden(esk7_0,esk6_1(X1))), inference(spm,[status(thm)],[c_0_48, c_0_105])).
% 8.46/8.69  cnf(c_0_113, negated_conjecture, (r2_hidden(esk7_0,esk6_1(k2_xboole_0(esk7_0,k1_tarski(esk7_0))))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_106]), c_0_95])).
% 8.46/8.69  cnf(c_0_114, negated_conjecture, (r2_hidden(esk8_0,esk7_0)|r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_107]), c_0_108])).
% 8.46/8.69  cnf(c_0_115, negated_conjecture, (r2_hidden(esk7_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_109, c_0_91])).
% 8.46/8.69  cnf(c_0_116, negated_conjecture, (r1_tarski(esk6_1(X1),esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0))|~r1_ordinal1(esk6_1(X1),esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0))), inference(spm,[status(thm)],[c_0_110, c_0_88])).
% 8.46/8.69  cnf(c_0_117, negated_conjecture, (r1_ordinal1(esk6_1(X1),esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0))|r2_hidden(esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0),X1)), inference(spm,[status(thm)],[c_0_111, c_0_104])).
% 8.46/8.69  cnf(c_0_118, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 8.46/8.69  cnf(c_0_119, negated_conjecture, (r1_tarski(esk7_0,esk6_1(k2_xboole_0(esk7_0,k1_tarski(esk7_0))))), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 8.46/8.69  cnf(c_0_120, negated_conjecture, (r1_ordinal1(esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_67, c_0_98])).
% 8.46/8.69  cnf(c_0_121, plain, (r2_hidden(X1,k1_ordinal1(X2))|~r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 8.46/8.69  cnf(c_0_122, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_72])).
% 8.46/8.69  cnf(c_0_123, negated_conjecture, (r2_hidden(esk8_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_114]), c_0_115])).
% 8.46/8.69  cnf(c_0_124, plain, (r1_tarski(esk6_1(X1),esk6_1(X2))|~r1_ordinal1(esk6_1(X1),esk6_1(X2))), inference(spm,[status(thm)],[c_0_92, c_0_88])).
% 8.46/8.69  cnf(c_0_125, plain, (r1_ordinal1(esk6_1(X1),esk6_1(X2))|r2_hidden(esk6_1(X2),X1)), inference(spm,[status(thm)],[c_0_111, c_0_88])).
% 8.46/8.69  cnf(c_0_126, negated_conjecture, (r2_hidden(esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0),X1)|r1_tarski(esk6_1(X1),esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0))), inference(spm,[status(thm)],[c_0_116, c_0_117])).
% 8.46/8.69  cnf(c_0_127, negated_conjecture, (r2_hidden(X1,esk6_1(k2_xboole_0(esk7_0,k1_tarski(esk7_0))))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_118, c_0_119])).
% 8.46/8.69  cnf(c_0_128, negated_conjecture, (r2_hidden(esk7_0,esk6_1(esk6_1(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))))|r2_hidden(esk6_1(esk6_1(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))),esk7_0)), inference(spm,[status(thm)],[c_0_101, c_0_113])).
% 8.46/8.69  cnf(c_0_129, negated_conjecture, (r1_tarski(esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_104]), c_0_120])])).
% 8.46/8.69  cnf(c_0_130, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r1_ordinal1(X1,X2)), inference(rw,[status(thm)],[c_0_121, c_0_40])).
% 8.46/8.69  cnf(c_0_131, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_122])).
% 8.46/8.69  cnf(c_0_132, negated_conjecture, (r2_hidden(esk8_0,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(spm,[status(thm)],[c_0_61, c_0_123])).
% 8.46/8.69  cnf(c_0_133, plain, (r2_hidden(esk6_1(X1),X2)|r1_tarski(esk6_1(X2),esk6_1(X1))), inference(spm,[status(thm)],[c_0_124, c_0_125])).
% 8.46/8.69  cnf(c_0_134, negated_conjecture, (r2_hidden(esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0),X1)|r2_hidden(X2,esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0))|~r2_hidden(X2,esk6_1(X1))), inference(spm,[status(thm)],[c_0_118, c_0_126])).
% 8.46/8.69  cnf(c_0_135, negated_conjecture, (r2_hidden(esk7_0,esk6_1(esk6_1(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_128]), c_0_95])).
% 8.46/8.69  cnf(c_0_136, negated_conjecture, (~r2_hidden(esk7_0,esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0))), inference(spm,[status(thm)],[c_0_48, c_0_129])).
% 8.46/8.69  cnf(c_0_137, negated_conjecture, (r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))|~r1_ordinal1(X1,esk7_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_130, c_0_22])).
% 8.46/8.69  cnf(c_0_138, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_48, c_0_131])).
% 8.46/8.69  cnf(c_0_139, negated_conjecture, (v3_ordinal1(esk8_0)), inference(spm,[status(thm)],[c_0_33, c_0_123])).
% 8.46/8.69  cnf(c_0_140, negated_conjecture, (r1_ordinal1(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_67, c_0_132])).
% 8.46/8.69  cnf(c_0_141, plain, (r2_hidden(esk6_1(X1),X2)|r2_hidden(X3,esk6_1(X1))|~r2_hidden(X3,esk6_1(X2))), inference(spm,[status(thm)],[c_0_118, c_0_133])).
% 8.46/8.69  cnf(c_0_142, negated_conjecture, (r2_hidden(esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0),esk6_1(k2_xboole_0(esk7_0,k1_tarski(esk7_0))))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_135]), c_0_136])).
% 8.46/8.69  cnf(c_0_143, negated_conjecture, (~r1_ordinal1(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_52]), c_0_138])).
% 8.46/8.69  fof(c_0_144, plain, ![X33]:X33!=k1_ordinal1(X33), inference(variable_rename,[status(thm)],[t14_ordinal1])).
% 8.46/8.69  cnf(c_0_145, negated_conjecture, (r1_tarski(esk8_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_139]), c_0_140])])).
% 8.46/8.69  cnf(c_0_146, negated_conjecture, (r2_hidden(esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0),esk6_1(X1))|r2_hidden(esk6_1(X1),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(spm,[status(thm)],[c_0_141, c_0_142])).
% 8.46/8.69  cnf(c_0_147, negated_conjecture, (r1_tarski(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))|~r1_ordinal1(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_66, c_0_52])).
% 8.46/8.69  cnf(c_0_148, negated_conjecture, (r1_ordinal1(esk7_0,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_52]), c_0_143])).
% 8.46/8.69  cnf(c_0_149, plain, (X1!=k1_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_144])).
% 8.46/8.69  cnf(c_0_150, negated_conjecture, (v3_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_45, c_0_139])).
% 8.46/8.69  cnf(c_0_151, negated_conjecture, (r1_tarski(X1,esk8_0)|~r1_ordinal1(X1,esk8_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_66, c_0_139])).
% 8.46/8.69  cnf(c_0_152, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_118, c_0_145])).
% 8.46/8.69  cnf(c_0_153, negated_conjecture, (r2_hidden(esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0),X1)|r2_hidden(esk6_1(X1),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_146]), c_0_138])).
% 8.46/8.69  cnf(c_0_154, negated_conjecture, (r1_tarski(esk7_0,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147, c_0_22]), c_0_148])])).
% 8.46/8.69  cnf(c_0_155, plain, (X1!=k2_xboole_0(X1,k1_tarski(X1))), inference(rw,[status(thm)],[c_0_149, c_0_40])).
% 8.46/8.69  cnf(c_0_156, negated_conjecture, (r1_tarski(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|~r1_ordinal1(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_66, c_0_150])).
% 8.46/8.69  cnf(c_0_157, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))|~r1_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_137, c_0_150])).
% 8.46/8.69  cnf(c_0_158, negated_conjecture, (r1_ordinal1(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|r1_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_89, c_0_150])).
% 8.46/8.69  cnf(c_0_159, negated_conjecture, (r1_tarski(esk6_1(X1),esk8_0)|~r1_ordinal1(esk6_1(X1),esk8_0)), inference(spm,[status(thm)],[c_0_151, c_0_88])).
% 8.46/8.69  cnf(c_0_160, negated_conjecture, (r1_ordinal1(esk6_1(X1),esk8_0)|r2_hidden(esk8_0,X1)), inference(spm,[status(thm)],[c_0_111, c_0_139])).
% 8.46/8.69  cnf(c_0_161, plain, (r2_hidden(X1,X2)|X1=X2|~r2_hidden(X1,k1_ordinal1(X2))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 8.46/8.69  cnf(c_0_162, negated_conjecture, (r2_hidden(esk1_2(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0),esk7_0)|r2_hidden(esk6_1(esk8_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(spm,[status(thm)],[c_0_152, c_0_153])).
% 8.46/8.69  cnf(c_0_163, negated_conjecture, (~r1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_154]), c_0_155])).
% 8.46/8.69  cnf(c_0_164, negated_conjecture, (r1_tarski(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|~r1_ordinal1(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_156, c_0_22])).
% 8.46/8.69  cnf(c_0_165, negated_conjecture, (r1_ordinal1(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(spm,[status(thm)],[c_0_157, c_0_158])).
% 8.46/8.69  cnf(c_0_166, negated_conjecture, (r2_hidden(esk8_0,X1)|r1_tarski(esk6_1(X1),esk8_0)), inference(spm,[status(thm)],[c_0_159, c_0_160])).
% 8.46/8.69  cnf(c_0_167, plain, (X1=X2|r2_hidden(X1,X2)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_161, c_0_40])).
% 8.46/8.69  cnf(c_0_168, negated_conjecture, (r2_hidden(esk6_1(esk8_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_162]), c_0_163])).
% 8.46/8.69  cnf(c_0_169, negated_conjecture, (r2_hidden(esk6_1(esk7_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_153]), c_0_163])).
% 8.46/8.69  cnf(c_0_170, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))|r1_tarski(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_164, c_0_165])).
% 8.46/8.69  cnf(c_0_171, negated_conjecture, (r2_hidden(esk8_0,X1)|~r2_hidden(esk8_0,esk6_1(X1))), inference(spm,[status(thm)],[c_0_48, c_0_166])).
% 8.46/8.69  cnf(c_0_172, negated_conjecture, (esk6_1(esk8_0)=esk7_0|r2_hidden(esk6_1(esk8_0),esk7_0)), inference(spm,[status(thm)],[c_0_167, c_0_168])).
% 8.46/8.69  cnf(c_0_173, negated_conjecture, (esk6_1(esk7_0)=esk7_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_167, c_0_169]), c_0_95])).
% 8.46/8.69  cnf(c_0_174, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))|r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_118, c_0_170])).
% 8.46/8.69  cnf(c_0_175, negated_conjecture, (r2_hidden(esk6_1(esk8_0),esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171, c_0_172]), c_0_123])]), c_0_138])).
% 8.46/8.69  cnf(c_0_176, plain, (X1=k3_tarski(X1)|~v4_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 8.46/8.69  cnf(c_0_177, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_63, c_0_123])).
% 8.46/8.69  cnf(c_0_178, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_30, c_0_150])).
% 8.46/8.69  cnf(c_0_179, negated_conjecture, (r2_hidden(esk6_1(X1),esk7_0)|r2_hidden(X2,esk6_1(X1))|~r2_hidden(X2,esk7_0)), inference(spm,[status(thm)],[c_0_141, c_0_173])).
% 8.46/8.69  cnf(c_0_180, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))|r2_hidden(esk6_1(esk8_0),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_174, c_0_175])).
% 8.46/8.69  cnf(c_0_181, negated_conjecture, (k3_tarski(esk7_0)=esk7_0|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_176, c_0_177])).
% 8.46/8.69  cnf(c_0_182, negated_conjecture, (r1_ordinal1(X1,esk8_0)|~r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_139]), c_0_178])).
% 8.46/8.69  cnf(c_0_183, negated_conjecture, (k2_xboole_0(esk8_0,k1_tarski(esk8_0))=esk7_0|r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_25, c_0_150])).
% 8.46/8.69  cnf(c_0_184, plain, (r2_hidden(esk6_1(X1),X2)|~r2_hidden(esk6_1(X1),esk6_1(X2))), inference(spm,[status(thm)],[c_0_48, c_0_133])).
% 8.46/8.69  cnf(c_0_185, negated_conjecture, (r2_hidden(esk6_1(esk8_0),esk6_1(X1))|r2_hidden(esk6_1(X1),esk7_0)), inference(spm,[status(thm)],[c_0_179, c_0_175])).
% 8.46/8.69  cnf(c_0_186, negated_conjecture, (r1_tarski(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|~r1_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_73, c_0_150])).
% 8.46/8.69  cnf(c_0_187, negated_conjecture, (r1_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|r2_hidden(esk6_1(esk8_0),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_67, c_0_180])).
% 8.46/8.69  cnf(c_0_188, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|r2_hidden(esk2_3(esk7_0,esk7_0,X1),esk7_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_90, c_0_181])).
% 8.46/8.69  cnf(c_0_189, negated_conjecture, (r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|~r1_ordinal1(X1,esk8_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_130, c_0_139])).
% 8.46/8.69  cnf(c_0_190, negated_conjecture, (r1_ordinal1(X1,esk8_0)|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_182, c_0_183])).
% 8.46/8.69  cnf(c_0_191, negated_conjecture, (r2_hidden(esk6_1(X1),esk7_0)|r2_hidden(esk6_1(esk8_0),X1)), inference(spm,[status(thm)],[c_0_184, c_0_185])).
% 8.46/8.69  cnf(c_0_192, negated_conjecture, (r2_hidden(esk6_1(esk8_0),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|r1_tarski(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_186, c_0_187])).
% 8.46/8.69  cnf(c_0_193, negated_conjecture, (r2_hidden(esk2_3(esk7_0,esk7_0,esk8_0),esk7_0)|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_188, c_0_123])).
% 8.46/8.69  cnf(c_0_194, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|r2_hidden(X1,esk2_3(esk7_0,esk7_0,X1))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_109, c_0_181])).
% 8.46/8.69  cnf(c_0_195, plain, (v3_ordinal1(k2_xboole_0(esk6_1(X1),k1_tarski(esk6_1(X1))))), inference(spm,[status(thm)],[c_0_45, c_0_88])).
% 8.46/8.69  cnf(c_0_196, negated_conjecture, (r2_hidden(esk6_1(X1),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|~r1_ordinal1(esk6_1(X1),esk8_0)), inference(spm,[status(thm)],[c_0_189, c_0_88])).
% 8.46/8.69  cnf(c_0_197, negated_conjecture, (r1_ordinal1(esk6_1(esk8_0),esk8_0)|r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_190, c_0_191]), c_0_173]), c_0_138])).
% 8.46/8.69  cnf(c_0_198, negated_conjecture, (r2_hidden(esk6_1(esk8_0),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|~r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_48, c_0_192])).
% 8.46/8.69  cnf(c_0_199, negated_conjecture, (r2_hidden(esk2_3(esk7_0,esk7_0,esk8_0),esk7_0)|r2_hidden(X1,k3_tarski(esk7_0))|~r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_69, c_0_193])).
% 8.46/8.69  cnf(c_0_200, negated_conjecture, (r2_hidden(esk8_0,esk2_3(esk7_0,esk7_0,esk8_0))|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_194, c_0_123])).
% 8.46/8.69  cnf(c_0_201, plain, (r1_ordinal1(esk6_1(X1),k2_xboole_0(esk6_1(X2),k1_tarski(esk6_1(X2))))|r2_hidden(k2_xboole_0(esk6_1(X2),k1_tarski(esk6_1(X2))),X1)), inference(spm,[status(thm)],[c_0_111, c_0_195])).
% 8.46/8.69  cnf(c_0_202, negated_conjecture, (r2_hidden(esk6_1(esk8_0),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_196, c_0_197]), c_0_198])).
% 8.46/8.69  cnf(c_0_203, negated_conjecture, (r2_hidden(esk2_3(esk7_0,esk7_0,esk8_0),esk7_0)|r2_hidden(esk8_0,k3_tarski(esk7_0))), inference(spm,[status(thm)],[c_0_199, c_0_76])).
% 8.46/8.69  cnf(c_0_204, negated_conjecture, (r2_hidden(esk8_0,esk2_3(esk7_0,esk7_0,esk8_0))|r2_hidden(X1,k3_tarski(esk7_0))|~r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_69, c_0_200])).
% 8.46/8.69  cnf(c_0_205, negated_conjecture, (r1_ordinal1(esk7_0,k2_xboole_0(esk6_1(X1),k1_tarski(esk6_1(X1))))|r2_hidden(k2_xboole_0(esk6_1(X1),k1_tarski(esk6_1(X1))),esk7_0)), inference(spm,[status(thm)],[c_0_201, c_0_173])).
% 8.46/8.69  cnf(c_0_206, negated_conjecture, (esk6_1(esk8_0)=esk8_0|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_167, c_0_202]), c_0_95])).
% 8.46/8.69  cnf(c_0_207, negated_conjecture, (r2_hidden(esk8_0,k3_tarski(esk7_0))|r2_hidden(X1,k3_tarski(esk7_0))|~r2_hidden(X1,esk2_3(esk7_0,esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_69, c_0_203])).
% 8.46/8.69  cnf(c_0_208, negated_conjecture, (r2_hidden(esk8_0,esk2_3(esk7_0,esk7_0,esk8_0))|r2_hidden(esk8_0,k3_tarski(esk7_0))), inference(spm,[status(thm)],[c_0_204, c_0_76])).
% 8.46/8.69  cnf(c_0_209, negated_conjecture, (r1_ordinal1(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_205, c_0_206])).
% 8.46/8.69  cnf(c_0_210, negated_conjecture, (r2_hidden(esk8_0,k3_tarski(esk7_0))), inference(spm,[status(thm)],[c_0_207, c_0_208])).
% 8.46/8.69  cnf(c_0_211, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|r1_tarski(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_164, c_0_209])).
% 8.46/8.69  cnf(c_0_212, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk7_0)), inference(spm,[status(thm)],[c_0_90, c_0_210])).
% 8.46/8.69  cnf(c_0_213, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_118, c_0_211])).
% 8.46/8.69  cnf(c_0_214, negated_conjecture, (v3_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0))), inference(spm,[status(thm)],[c_0_33, c_0_212])).
% 8.46/8.69  cnf(c_0_215, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_213, c_0_212])).
% 8.46/8.69  cnf(c_0_216, negated_conjecture, (~r2_hidden(k1_ordinal1(esk8_0),esk7_0)|~v4_ordinal1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 8.46/8.69  cnf(c_0_217, negated_conjecture, (r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)|~r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_151, c_0_214])).
% 8.46/8.69  cnf(c_0_218, negated_conjecture, (r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_182, c_0_215])).
% 8.46/8.69  cnf(c_0_219, negated_conjecture, (~v4_ordinal1(esk7_0)|~r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(rw,[status(thm)],[c_0_216, c_0_40])).
% 8.46/8.69  cnf(c_0_220, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_217, c_0_218])).
% 8.46/8.69  cnf(c_0_221, negated_conjecture, (r2_hidden(esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0))), inference(spm,[status(thm)],[c_0_109, c_0_210])).
% 8.46/8.69  cnf(c_0_222, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk5_1(esk7_0),esk7_0)|~r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_219, c_0_32])).
% 8.46/8.69  cnf(c_0_223, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_220]), c_0_221])])).
% 8.46/8.69  cnf(c_0_224, negated_conjecture, (r2_hidden(esk5_1(esk7_0),esk7_0)|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_222, c_0_223])])).
% 8.46/8.69  cnf(c_0_225, negated_conjecture, (v3_ordinal1(esk5_1(esk7_0))|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(k3_tarski(esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_33, c_0_224])).
% 8.46/8.69  cnf(c_0_226, negated_conjecture, (v3_ordinal1(k3_tarski(esk7_0))|r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_225]), c_0_33])).
% 8.46/8.69  cnf(c_0_227, negated_conjecture, (k3_tarski(esk7_0)=esk7_0|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(k3_tarski(esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_25, c_0_226])).
% 8.46/8.69  cnf(c_0_228, negated_conjecture, (~v4_ordinal1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_219, c_0_223])])).
% 8.46/8.69  cnf(c_0_229, negated_conjecture, (r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_227]), c_0_228])).
% 8.46/8.69  cnf(c_0_230, negated_conjecture, (r2_hidden(k2_xboole_0(k3_tarski(esk7_0),k1_tarski(k3_tarski(esk7_0))),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_229]), c_0_228])).
% 8.46/8.69  cnf(c_0_231, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(X1,k3_tarski(esk7_0))|~r2_hidden(X1,k2_xboole_0(k3_tarski(esk7_0),k1_tarski(k3_tarski(esk7_0))))), inference(spm,[status(thm)],[c_0_69, c_0_230])).
% 8.46/8.69  cnf(c_0_232, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_231, c_0_76]), c_0_138])).
% 8.46/8.69  cnf(c_0_233, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_90, c_0_232])).
% 8.46/8.69  cnf(c_0_234, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(spm,[status(thm)],[c_0_61, c_0_233])).
% 8.46/8.69  cnf(c_0_235, negated_conjecture, (v3_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0))), inference(spm,[status(thm)],[c_0_33, c_0_233])).
% 8.46/8.69  cnf(c_0_236, negated_conjecture, (r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_67, c_0_234])).
% 8.46/8.69  cnf(c_0_237, negated_conjecture, (r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_235]), c_0_236])])).
% 8.46/8.69  cnf(c_0_238, negated_conjecture, (r2_hidden(esk7_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0))), inference(spm,[status(thm)],[c_0_109, c_0_232])).
% 8.46/8.69  cnf(c_0_239, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_237]), c_0_238])]), ['proof']).
% 8.46/8.69  # SZS output end CNFRefutation
% 8.46/8.69  # Proof object total steps             : 240
% 8.46/8.69  # Proof object clause steps            : 203
% 8.46/8.69  # Proof object formula steps           : 37
% 8.46/8.69  # Proof object conjectures             : 156
% 8.46/8.69  # Proof object clause conjectures      : 153
% 8.46/8.69  # Proof object formula conjectures     : 3
% 8.46/8.69  # Proof object initial clauses used    : 32
% 8.46/8.69  # Proof object initial formulas used   : 18
% 8.46/8.69  # Proof object generating inferences   : 155
% 8.46/8.69  # Proof object simplifying inferences  : 61
% 8.46/8.69  # Training examples: 0 positive, 0 negative
% 8.46/8.69  # Parsed axioms                        : 18
% 8.46/8.69  # Removed by relevancy pruning/SinE    : 0
% 8.46/8.69  # Initial clauses                      : 39
% 8.46/8.69  # Removed in clause preprocessing      : 1
% 8.46/8.69  # Initial clauses in saturation        : 38
% 8.46/8.69  # Processed clauses                    : 16102
% 8.46/8.69  # ...of these trivial                  : 433
% 8.46/8.69  # ...subsumed                          : 9071
% 8.46/8.69  # ...remaining for further processing  : 6598
% 8.46/8.69  # Other redundant clauses eliminated   : 686
% 8.46/8.69  # Clauses deleted for lack of memory   : 0
% 8.46/8.69  # Backward-subsumed                    : 834
% 8.46/8.69  # Backward-rewritten                   : 1321
% 8.46/8.69  # Generated clauses                    : 847179
% 8.46/8.69  # ...of the previous two non-trivial   : 735317
% 8.46/8.69  # Contextual simplify-reflections      : 86
% 8.46/8.69  # Paramodulations                      : 846443
% 8.46/8.69  # Factorizations                       : 4
% 8.46/8.69  # Equation resolutions                 : 686
% 8.46/8.69  # Propositional unsat checks           : 0
% 8.46/8.69  #    Propositional check models        : 0
% 8.46/8.69  #    Propositional check unsatisfiable : 0
% 8.46/8.69  #    Propositional clauses             : 0
% 8.46/8.69  #    Propositional clauses after purity: 0
% 8.46/8.69  #    Propositional unsat core size     : 0
% 8.46/8.69  #    Propositional preprocessing time  : 0.000
% 8.46/8.69  #    Propositional encoding time       : 0.000
% 8.46/8.69  #    Propositional solver time         : 0.000
% 8.46/8.69  #    Success case prop preproc time    : 0.000
% 8.46/8.69  #    Success case prop encoding time   : 0.000
% 8.46/8.69  #    Success case prop solver time     : 0.000
% 8.46/8.69  # Current number of processed clauses  : 4355
% 8.46/8.69  #    Positive orientable unit clauses  : 687
% 8.46/8.69  #    Positive unorientable unit clauses: 0
% 8.46/8.69  #    Negative unit clauses             : 97
% 8.46/8.69  #    Non-unit-clauses                  : 3571
% 8.46/8.69  # Current number of unprocessed clauses: 716266
% 8.46/8.69  # ...number of literals in the above   : 3780139
% 8.46/8.69  # Current number of archived formulas  : 0
% 8.46/8.69  # Current number of archived clauses   : 2238
% 8.46/8.69  # Clause-clause subsumption calls (NU) : 2281394
% 8.46/8.69  # Rec. Clause-clause subsumption calls : 757664
% 8.46/8.69  # Non-unit clause-clause subsumptions  : 7539
% 8.46/8.69  # Unit Clause-clause subsumption calls : 232215
% 8.46/8.69  # Rewrite failures with RHS unbound    : 0
% 8.46/8.69  # BW rewrite match attempts            : 1713
% 8.46/8.69  # BW rewrite match successes           : 121
% 8.46/8.69  # Condensation attempts                : 0
% 8.46/8.69  # Condensation successes               : 0
% 8.46/8.69  # Termbank termtop insertions          : 23313412
% 8.46/8.72  
% 8.46/8.72  # -------------------------------------------------
% 8.46/8.72  # User time                : 8.045 s
% 8.46/8.72  # System time              : 0.274 s
% 8.46/8.72  # Total time               : 8.319 s
% 8.46/8.72  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
