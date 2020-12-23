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
% DateTime   : Thu Dec  3 10:56:33 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :  149 (92936 expanded)
%              Number of clauses        :  116 (41535 expanded)
%              Number of leaves         :   16 (21851 expanded)
%              Depth                    :   48
%              Number of atoms          :  424 (377957 expanded)
%              Number of equality atoms :   37 (30738 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_ordinal1)).

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(t35_ordinal1,axiom,(
    ! [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
         => v3_ordinal1(X2) )
     => v3_ordinal1(k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_ordinal1)).

fof(d6_ordinal1,axiom,(
    ! [X1] :
      ( v4_ordinal1(X1)
    <=> X1 = k3_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_ordinal1)).

fof(t23_ordinal1,axiom,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ( r2_hidden(X1,X2)
       => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(t29_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k1_ordinal1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(t34_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,k1_ordinal1(X2))
          <=> r1_ordinal1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(t13_ordinal1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,k1_ordinal1(X2))
    <=> ( r2_hidden(X1,X2)
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(t33_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
          <=> r1_ordinal1(k1_ordinal1(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ( v4_ordinal1(X1)
        <=> ! [X2] :
              ( v3_ordinal1(X2)
             => ( r2_hidden(X2,X1)
               => r2_hidden(k1_ordinal1(X2),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t41_ordinal1])).

fof(c_0_17,plain,(
    ! [X35,X36] :
      ( ~ v3_ordinal1(X35)
      | ~ v3_ordinal1(X36)
      | r2_hidden(X35,X36)
      | X35 = X36
      | r2_hidden(X36,X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

fof(c_0_18,negated_conjecture,(
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
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])])])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( v3_ordinal1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_21,plain,(
    ! [X42] :
      ( ( r2_hidden(esk5_1(X42),X42)
        | v3_ordinal1(k3_tarski(X42)) )
      & ( ~ v3_ordinal1(esk5_1(X42))
        | v3_ordinal1(k3_tarski(X42)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_ordinal1])])])])).

fof(c_0_22,plain,(
    ! [X27] :
      ( ( ~ v4_ordinal1(X27)
        | X27 = k3_tarski(X27) )
      & ( X27 != k3_tarski(X27)
        | v4_ordinal1(X27) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_ordinal1])])).

cnf(c_0_23,negated_conjecture,
    ( X1 = esk7_0
    | r2_hidden(X1,esk7_0)
    | r2_hidden(esk7_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( r2_hidden(esk5_1(X1),X1)
    | v3_ordinal1(k3_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X33,X34] :
      ( ~ v3_ordinal1(X34)
      | ~ r2_hidden(X33,X34)
      | v3_ordinal1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

cnf(c_0_26,plain,
    ( v4_ordinal1(X1)
    | X1 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( k3_tarski(X1) = esk7_0
    | r2_hidden(esk7_0,k3_tarski(X1))
    | r2_hidden(k3_tarski(X1),esk7_0)
    | r2_hidden(esk5_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0)
    | ~ v4_ordinal1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( v4_ordinal1(esk7_0)
    | r2_hidden(esk5_1(esk7_0),esk7_0)
    | r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27])])).

cnf(c_0_31,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk5_1(esk7_0),esk7_0)
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,plain,
    ( v3_ordinal1(k3_tarski(X1))
    | ~ v3_ordinal1(esk5_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( v3_ordinal1(esk5_1(esk7_0))
    | r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_35,plain,(
    ! [X26] : k1_ordinal1(X26) = k2_xboole_0(X26,k1_tarski(X26)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_36,plain,(
    ! [X46,X47] :
      ( ~ r2_hidden(X46,X47)
      | ~ r1_tarski(X47,X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_37,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_38,negated_conjecture,
    ( v3_ordinal1(k3_tarski(esk7_0))
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( v4_ordinal1(esk7_0)
    | r2_hidden(k1_ordinal1(X1),esk7_0)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_40,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( k3_tarski(esk7_0) = esk7_0
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_38])).

fof(c_0_44,plain,(
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

cnf(c_0_45,negated_conjecture,
    ( v4_ordinal1(esk7_0)
    | r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk7_0)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_43]),c_0_29])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( v4_ordinal1(esk7_0)
    | r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(csr,[status(thm)],[c_0_45,c_0_31])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,k3_tarski(esk7_0)),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_51,plain,(
    ! [X30] : r2_hidden(X30,k1_ordinal1(X30)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk1_2(esk7_0,k3_tarski(esk7_0)),k1_tarski(esk1_2(esk7_0,k3_tarski(esk7_0)))),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_29])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_55,plain,(
    ! [X37] :
      ( ~ v3_ordinal1(X37)
      | v3_ordinal1(k1_ordinal1(X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(X1,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk1_2(esk7_0,k3_tarski(esk7_0)),k1_tarski(esk1_2(esk7_0,k3_tarski(esk7_0))))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_54,c_0_40])).

cnf(c_0_58,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,k3_tarski(esk7_0)),k3_tarski(esk7_0))
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

fof(c_0_61,plain,(
    ! [X40,X41] :
      ( ( ~ r2_hidden(X40,k1_ordinal1(X41))
        | r1_ordinal1(X40,X41)
        | ~ v3_ordinal1(X41)
        | ~ v3_ordinal1(X40) )
      & ( ~ r1_ordinal1(X40,X41)
        | r2_hidden(X40,k1_ordinal1(X41))
        | ~ v3_ordinal1(X41)
        | ~ v3_ordinal1(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).

cnf(c_0_62,plain,
    ( v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[c_0_58,c_0_40])).

fof(c_0_63,plain,(
    ! [X31,X32] :
      ( ( ~ r2_hidden(X31,k1_ordinal1(X32))
        | r2_hidden(X31,X32)
        | X31 = X32 )
      & ( ~ r2_hidden(X31,X32)
        | r2_hidden(X31,k1_ordinal1(X32)) )
      & ( X31 != X32
        | r2_hidden(X31,k1_ordinal1(X32)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).

cnf(c_0_64,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0)
    | r1_tarski(esk7_0,k3_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,plain,
    ( r1_ordinal1(X1,X2)
    | ~ r2_hidden(X1,k1_ordinal1(X2))
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( v3_ordinal1(k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_20])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_69,plain,
    ( r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_65]),c_0_47])).

fof(c_0_71,plain,(
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

cnf(c_0_72,plain,
    ( r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_66,c_0_40])).

cnf(c_0_73,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_67])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_68,c_0_40])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( r1_ordinal1(X1,esk7_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_20]),c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k3_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(X1,esk7_0)
    | ~ r1_ordinal1(X1,esk7_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_20])).

cnf(c_0_81,negated_conjecture,
    ( v3_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_83,plain,
    ( r2_hidden(X1,esk2_3(X2,k3_tarski(X2),X1))
    | ~ r2_hidden(X1,k3_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0)
    | r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk7_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_70])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_84]),c_0_85])).

cnf(c_0_87,plain,
    ( X1 = k3_tarski(X1)
    | ~ v4_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_88,negated_conjecture,
    ( v4_ordinal1(esk7_0)
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_86])).

cnf(c_0_89,negated_conjecture,
    ( k3_tarski(esk7_0) = esk7_0
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

fof(c_0_90,plain,(
    ! [X38,X39] :
      ( ( ~ r2_hidden(X38,X39)
        | r1_ordinal1(k1_ordinal1(X38),X39)
        | ~ v3_ordinal1(X39)
        | ~ v3_ordinal1(X38) )
      & ( ~ r1_ordinal1(k1_ordinal1(X38),X39)
        | r2_hidden(X38,X39)
        | ~ v3_ordinal1(X39)
        | ~ v3_ordinal1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_ordinal1])])])])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | r2_hidden(esk2_3(esk7_0,esk7_0,X1),esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_89])).

cnf(c_0_92,plain,
    ( r1_ordinal1(k1_ordinal1(X1),X2)
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,esk7_0,esk8_0),esk7_0)
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_86])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | r2_hidden(X1,esk2_3(esk7_0,esk7_0,X1))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_89])).

cnf(c_0_95,plain,
    ( r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_92,c_0_40])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,esk7_0,esk8_0),esk7_0)
    | r2_hidden(X1,k3_tarski(esk7_0))
    | ~ r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_93])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(esk8_0,esk2_3(esk7_0,esk7_0,esk8_0))
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_86])).

cnf(c_0_98,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_99,plain,
    ( r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_95,c_0_28])).

cnf(c_0_100,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,esk7_0,esk8_0),esk7_0)
    | r2_hidden(esk8_0,k3_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_57])).

cnf(c_0_101,negated_conjecture,
    ( r2_hidden(esk8_0,esk2_3(esk7_0,esk7_0,esk8_0))
    | r2_hidden(X1,k3_tarski(esk7_0))
    | ~ r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_97])).

cnf(c_0_102,negated_conjecture,
    ( v3_ordinal1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_86])).

cnf(c_0_103,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r1_ordinal1(X1,X2) ),
    inference(rw,[status(thm)],[c_0_98,c_0_40])).

cnf(c_0_104,negated_conjecture,
    ( r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_20])).

cnf(c_0_105,negated_conjecture,
    ( r2_hidden(esk8_0,k3_tarski(esk7_0))
    | r2_hidden(X1,k3_tarski(esk7_0))
    | ~ r2_hidden(X1,esk2_3(esk7_0,esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_100])).

cnf(c_0_106,negated_conjecture,
    ( r2_hidden(esk8_0,esk2_3(esk7_0,esk7_0,esk8_0))
    | r2_hidden(esk8_0,k3_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_57])).

cnf(c_0_107,negated_conjecture,
    ( v3_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_102])).

cnf(c_0_108,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | ~ r2_hidden(X1,k1_ordinal1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_109,negated_conjecture,
    ( r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))
    | ~ r1_ordinal1(X1,esk7_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_103,c_0_20])).

cnf(c_0_110,negated_conjecture,
    ( r1_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_104,c_0_86])).

cnf(c_0_111,negated_conjecture,
    ( r2_hidden(esk8_0,k3_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_112,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_107])).

cnf(c_0_113,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_108,c_0_40])).

cnf(c_0_114,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_107]),c_0_110])])).

cnf(c_0_115,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_111])).

cnf(c_0_116,negated_conjecture,
    ( r1_ordinal1(X1,esk8_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_102]),c_0_112])).

cnf(c_0_117,negated_conjecture,
    ( k2_xboole_0(esk8_0,k1_tarski(esk8_0)) = esk7_0
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_113,c_0_114])).

cnf(c_0_118,negated_conjecture,
    ( r1_tarski(X1,esk8_0)
    | ~ r1_ordinal1(X1,esk8_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_102])).

cnf(c_0_119,negated_conjecture,
    ( v3_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_115])).

cnf(c_0_120,negated_conjecture,
    ( r1_ordinal1(X1,esk8_0)
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_121,negated_conjecture,
    ( ~ r2_hidden(k1_ordinal1(esk8_0),esk7_0)
    | ~ v4_ordinal1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_122,negated_conjecture,
    ( r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)
    | ~ r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_123,negated_conjecture,
    ( r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_120,c_0_115])).

cnf(c_0_124,negated_conjecture,
    ( ~ v4_ordinal1(esk7_0)
    | ~ r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(rw,[status(thm)],[c_0_121,c_0_40])).

cnf(c_0_125,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_122,c_0_123])).

cnf(c_0_126,negated_conjecture,
    ( r2_hidden(esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_111])).

cnf(c_0_127,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk5_1(esk7_0),esk7_0)
    | ~ r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_124,c_0_30])).

cnf(c_0_128,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_125]),c_0_126])])).

cnf(c_0_129,negated_conjecture,
    ( r2_hidden(esk5_1(esk7_0),esk7_0)
    | r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_127,c_0_128])])).

cnf(c_0_130,negated_conjecture,
    ( v3_ordinal1(esk5_1(esk7_0))
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(k3_tarski(esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_129])).

cnf(c_0_131,negated_conjecture,
    ( v3_ordinal1(k3_tarski(esk7_0))
    | r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_130]),c_0_31])).

cnf(c_0_132,negated_conjecture,
    ( k3_tarski(esk7_0) = esk7_0
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(k3_tarski(esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_131])).

cnf(c_0_133,negated_conjecture,
    ( ~ v4_ordinal1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_124,c_0_128])])).

fof(c_0_134,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_135,negated_conjecture,
    ( r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_132]),c_0_133])).

cnf(c_0_136,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_134])).

cnf(c_0_137,negated_conjecture,
    ( r2_hidden(k2_xboole_0(k3_tarski(esk7_0),k1_tarski(k3_tarski(esk7_0))),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_135]),c_0_133])).

cnf(c_0_138,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_136])).

cnf(c_0_139,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(X1,k3_tarski(esk7_0))
    | ~ r2_hidden(X1,k2_xboole_0(k3_tarski(esk7_0),k1_tarski(k3_tarski(esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_137])).

cnf(c_0_140,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_138])).

cnf(c_0_141,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_57]),c_0_140])).

cnf(c_0_142,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_141])).

cnf(c_0_143,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_142])).

cnf(c_0_144,negated_conjecture,
    ( v3_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_142])).

cnf(c_0_145,negated_conjecture,
    ( r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_143])).

cnf(c_0_146,negated_conjecture,
    ( r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_144]),c_0_145])])).

cnf(c_0_147,negated_conjecture,
    ( r2_hidden(esk7_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_141])).

cnf(c_0_148,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_146]),c_0_147])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:41:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 2.05/2.23  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 2.05/2.23  # and selection function SelectCQIArEqFirst.
% 2.05/2.23  #
% 2.05/2.23  # Preprocessing time       : 0.053 s
% 2.05/2.23  # Presaturation interreduction done
% 2.05/2.23  
% 2.05/2.23  # Proof found!
% 2.05/2.23  # SZS status Theorem
% 2.05/2.23  # SZS output start CNFRefutation
% 2.05/2.23  fof(t41_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_ordinal1)).
% 2.05/2.23  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 2.05/2.23  fof(t35_ordinal1, axiom, ![X1]:(![X2]:(r2_hidden(X2,X1)=>v3_ordinal1(X2))=>v3_ordinal1(k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_ordinal1)).
% 2.05/2.23  fof(d6_ordinal1, axiom, ![X1]:(v4_ordinal1(X1)<=>X1=k3_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_ordinal1)).
% 2.05/2.23  fof(t23_ordinal1, axiom, ![X1, X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>v3_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 2.05/2.23  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 2.05/2.23  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.05/2.23  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.05/2.23  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 2.05/2.23  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 2.05/2.23  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 2.05/2.23  fof(t34_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 2.05/2.23  fof(t13_ordinal1, axiom, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 2.05/2.23  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 2.05/2.23  fof(t33_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)<=>r1_ordinal1(k1_ordinal1(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 2.05/2.23  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.05/2.23  fof(c_0_16, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1)))))), inference(assume_negation,[status(cth)],[t41_ordinal1])).
% 2.05/2.23  fof(c_0_17, plain, ![X35, X36]:(~v3_ordinal1(X35)|(~v3_ordinal1(X36)|(r2_hidden(X35,X36)|X35=X36|r2_hidden(X36,X35)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 2.05/2.23  fof(c_0_18, negated_conjecture, ![X50]:(v3_ordinal1(esk7_0)&(((v3_ordinal1(esk8_0)|~v4_ordinal1(esk7_0))&((r2_hidden(esk8_0,esk7_0)|~v4_ordinal1(esk7_0))&(~r2_hidden(k1_ordinal1(esk8_0),esk7_0)|~v4_ordinal1(esk7_0))))&(v4_ordinal1(esk7_0)|(~v3_ordinal1(X50)|(~r2_hidden(X50,esk7_0)|r2_hidden(k1_ordinal1(X50),esk7_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])])])).
% 2.05/2.23  cnf(c_0_19, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.05/2.23  cnf(c_0_20, negated_conjecture, (v3_ordinal1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.05/2.23  fof(c_0_21, plain, ![X42]:((r2_hidden(esk5_1(X42),X42)|v3_ordinal1(k3_tarski(X42)))&(~v3_ordinal1(esk5_1(X42))|v3_ordinal1(k3_tarski(X42)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_ordinal1])])])])).
% 2.05/2.23  fof(c_0_22, plain, ![X27]:((~v4_ordinal1(X27)|X27=k3_tarski(X27))&(X27!=k3_tarski(X27)|v4_ordinal1(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_ordinal1])])).
% 2.05/2.23  cnf(c_0_23, negated_conjecture, (X1=esk7_0|r2_hidden(X1,esk7_0)|r2_hidden(esk7_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 2.05/2.23  cnf(c_0_24, plain, (r2_hidden(esk5_1(X1),X1)|v3_ordinal1(k3_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.05/2.23  fof(c_0_25, plain, ![X33, X34]:(~v3_ordinal1(X34)|(~r2_hidden(X33,X34)|v3_ordinal1(X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).
% 2.05/2.23  cnf(c_0_26, plain, (v4_ordinal1(X1)|X1!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.05/2.23  cnf(c_0_27, negated_conjecture, (k3_tarski(X1)=esk7_0|r2_hidden(esk7_0,k3_tarski(X1))|r2_hidden(k3_tarski(X1),esk7_0)|r2_hidden(esk5_1(X1),X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 2.05/2.23  cnf(c_0_28, plain, (v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 2.05/2.23  cnf(c_0_29, negated_conjecture, (r2_hidden(esk8_0,esk7_0)|~v4_ordinal1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.05/2.23  cnf(c_0_30, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(esk5_1(esk7_0),esk7_0)|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27])])).
% 2.05/2.23  cnf(c_0_31, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_28, c_0_20])).
% 2.05/2.23  cnf(c_0_32, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk5_1(esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 2.05/2.23  cnf(c_0_33, plain, (v3_ordinal1(k3_tarski(X1))|~v3_ordinal1(esk5_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.05/2.23  cnf(c_0_34, negated_conjecture, (v3_ordinal1(esk5_1(esk7_0))|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 2.05/2.23  fof(c_0_35, plain, ![X26]:k1_ordinal1(X26)=k2_xboole_0(X26,k1_tarski(X26)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 2.05/2.23  fof(c_0_36, plain, ![X46, X47]:(~r2_hidden(X46,X47)|~r1_tarski(X47,X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 2.05/2.23  fof(c_0_37, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 2.05/2.23  cnf(c_0_38, negated_conjecture, (v3_ordinal1(k3_tarski(esk7_0))|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_31])).
% 2.05/2.23  cnf(c_0_39, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(k1_ordinal1(X1),esk7_0)|~v3_ordinal1(X1)|~r2_hidden(X1,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.05/2.23  cnf(c_0_40, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 2.05/2.23  cnf(c_0_41, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 2.05/2.23  cnf(c_0_42, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 2.05/2.23  cnf(c_0_43, negated_conjecture, (k3_tarski(esk7_0)=esk7_0|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_23, c_0_38])).
% 2.05/2.23  fof(c_0_44, plain, ![X13, X14, X15, X17, X18, X19, X20, X22]:((((r2_hidden(X15,esk2_3(X13,X14,X15))|~r2_hidden(X15,X14)|X14!=k3_tarski(X13))&(r2_hidden(esk2_3(X13,X14,X15),X13)|~r2_hidden(X15,X14)|X14!=k3_tarski(X13)))&(~r2_hidden(X17,X18)|~r2_hidden(X18,X13)|r2_hidden(X17,X14)|X14!=k3_tarski(X13)))&((~r2_hidden(esk3_2(X19,X20),X20)|(~r2_hidden(esk3_2(X19,X20),X22)|~r2_hidden(X22,X19))|X20=k3_tarski(X19))&((r2_hidden(esk3_2(X19,X20),esk4_2(X19,X20))|r2_hidden(esk3_2(X19,X20),X20)|X20=k3_tarski(X19))&(r2_hidden(esk4_2(X19,X20),X19)|r2_hidden(esk3_2(X19,X20),X20)|X20=k3_tarski(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 2.05/2.23  cnf(c_0_45, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk7_0)|~v3_ordinal1(X1)|~r2_hidden(X1,esk7_0)), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 2.05/2.23  cnf(c_0_46, plain, (r2_hidden(esk1_2(X1,X2),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 2.05/2.23  cnf(c_0_47, negated_conjecture, (r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_43]), c_0_29])).
% 2.05/2.23  cnf(c_0_48, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 2.05/2.23  cnf(c_0_49, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk7_0)|~r2_hidden(X1,esk7_0)), inference(csr,[status(thm)],[c_0_45, c_0_31])).
% 2.05/2.23  cnf(c_0_50, negated_conjecture, (r2_hidden(esk1_2(esk7_0,k3_tarski(esk7_0)),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 2.05/2.23  fof(c_0_51, plain, ![X30]:r2_hidden(X30,k1_ordinal1(X30)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 2.05/2.23  cnf(c_0_52, plain, (r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X3,X2)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_48])).
% 2.05/2.23  cnf(c_0_53, negated_conjecture, (r2_hidden(k2_xboole_0(esk1_2(esk7_0,k3_tarski(esk7_0)),k1_tarski(esk1_2(esk7_0,k3_tarski(esk7_0)))),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_29])).
% 2.05/2.23  cnf(c_0_54, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 2.05/2.23  fof(c_0_55, plain, ![X37]:(~v3_ordinal1(X37)|v3_ordinal1(k1_ordinal1(X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 2.05/2.23  cnf(c_0_56, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(X1,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)|~r2_hidden(X1,k2_xboole_0(esk1_2(esk7_0,k3_tarski(esk7_0)),k1_tarski(esk1_2(esk7_0,k3_tarski(esk7_0)))))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 2.05/2.23  cnf(c_0_57, plain, (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_54, c_0_40])).
% 2.05/2.23  cnf(c_0_58, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 2.05/2.23  cnf(c_0_59, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 2.05/2.23  cnf(c_0_60, negated_conjecture, (r2_hidden(esk1_2(esk7_0,k3_tarski(esk7_0)),k3_tarski(esk7_0))|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 2.05/2.23  fof(c_0_61, plain, ![X40, X41]:((~r2_hidden(X40,k1_ordinal1(X41))|r1_ordinal1(X40,X41)|~v3_ordinal1(X41)|~v3_ordinal1(X40))&(~r1_ordinal1(X40,X41)|r2_hidden(X40,k1_ordinal1(X41))|~v3_ordinal1(X41)|~v3_ordinal1(X40))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).
% 2.05/2.23  cnf(c_0_62, plain, (v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_58, c_0_40])).
% 2.05/2.23  fof(c_0_63, plain, ![X31, X32]:((~r2_hidden(X31,k1_ordinal1(X32))|(r2_hidden(X31,X32)|X31=X32))&((~r2_hidden(X31,X32)|r2_hidden(X31,k1_ordinal1(X32)))&(X31!=X32|r2_hidden(X31,k1_ordinal1(X32))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).
% 2.05/2.23  cnf(c_0_64, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|X2!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 2.05/2.23  cnf(c_0_65, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)|r1_tarski(esk7_0,k3_tarski(esk7_0))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 2.05/2.23  cnf(c_0_66, plain, (r1_ordinal1(X1,X2)|~r2_hidden(X1,k1_ordinal1(X2))|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 2.05/2.23  cnf(c_0_67, negated_conjecture, (v3_ordinal1(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(spm,[status(thm)],[c_0_62, c_0_20])).
% 2.05/2.23  cnf(c_0_68, plain, (r2_hidden(X1,k1_ordinal1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 2.05/2.23  cnf(c_0_69, plain, (r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)|~r2_hidden(X2,k3_tarski(X1))), inference(er,[status(thm)],[c_0_64])).
% 2.05/2.23  cnf(c_0_70, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_65]), c_0_47])).
% 2.05/2.23  fof(c_0_71, plain, ![X28, X29]:((~r1_ordinal1(X28,X29)|r1_tarski(X28,X29)|(~v3_ordinal1(X28)|~v3_ordinal1(X29)))&(~r1_tarski(X28,X29)|r1_ordinal1(X28,X29)|(~v3_ordinal1(X28)|~v3_ordinal1(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 2.05/2.23  cnf(c_0_72, plain, (r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_66, c_0_40])).
% 2.05/2.23  cnf(c_0_73, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(spm,[status(thm)],[c_0_28, c_0_67])).
% 2.05/2.23  cnf(c_0_74, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_68, c_0_40])).
% 2.05/2.23  cnf(c_0_75, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 2.05/2.23  cnf(c_0_76, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 2.05/2.23  cnf(c_0_77, negated_conjecture, (r1_ordinal1(X1,esk7_0)|~r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_20]), c_0_73])).
% 2.05/2.23  cnf(c_0_78, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 2.05/2.23  cnf(c_0_79, plain, (r2_hidden(X1,esk2_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k3_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 2.05/2.23  cnf(c_0_80, negated_conjecture, (r1_tarski(X1,esk7_0)|~r1_ordinal1(X1,esk7_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_76, c_0_20])).
% 2.05/2.23  cnf(c_0_81, negated_conjecture, (v3_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_31, c_0_75])).
% 2.05/2.23  cnf(c_0_82, negated_conjecture, (r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 2.05/2.23  cnf(c_0_83, plain, (r2_hidden(X1,esk2_3(X2,k3_tarski(X2),X1))|~r2_hidden(X1,k3_tarski(X2))), inference(er,[status(thm)],[c_0_79])).
% 2.05/2.23  cnf(c_0_84, negated_conjecture, (r2_hidden(esk8_0,esk7_0)|r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82])).
% 2.05/2.23  cnf(c_0_85, negated_conjecture, (r2_hidden(esk7_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_83, c_0_70])).
% 2.05/2.23  cnf(c_0_86, negated_conjecture, (r2_hidden(esk8_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_84]), c_0_85])).
% 2.05/2.23  cnf(c_0_87, plain, (X1=k3_tarski(X1)|~v4_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.05/2.23  cnf(c_0_88, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_49, c_0_86])).
% 2.05/2.23  cnf(c_0_89, negated_conjecture, (k3_tarski(esk7_0)=esk7_0|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 2.05/2.23  fof(c_0_90, plain, ![X38, X39]:((~r2_hidden(X38,X39)|r1_ordinal1(k1_ordinal1(X38),X39)|~v3_ordinal1(X39)|~v3_ordinal1(X38))&(~r1_ordinal1(k1_ordinal1(X38),X39)|r2_hidden(X38,X39)|~v3_ordinal1(X39)|~v3_ordinal1(X38))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_ordinal1])])])])).
% 2.05/2.23  cnf(c_0_91, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|r2_hidden(esk2_3(esk7_0,esk7_0,X1),esk7_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_69, c_0_89])).
% 2.05/2.23  cnf(c_0_92, plain, (r1_ordinal1(k1_ordinal1(X1),X2)|~r2_hidden(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 2.05/2.23  cnf(c_0_93, negated_conjecture, (r2_hidden(esk2_3(esk7_0,esk7_0,esk8_0),esk7_0)|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_91, c_0_86])).
% 2.05/2.23  cnf(c_0_94, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|r2_hidden(X1,esk2_3(esk7_0,esk7_0,X1))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_83, c_0_89])).
% 2.05/2.23  cnf(c_0_95, plain, (r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_92, c_0_40])).
% 2.05/2.23  cnf(c_0_96, negated_conjecture, (r2_hidden(esk2_3(esk7_0,esk7_0,esk8_0),esk7_0)|r2_hidden(X1,k3_tarski(esk7_0))|~r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_52, c_0_93])).
% 2.05/2.23  cnf(c_0_97, negated_conjecture, (r2_hidden(esk8_0,esk2_3(esk7_0,esk7_0,esk8_0))|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_94, c_0_86])).
% 2.05/2.23  cnf(c_0_98, plain, (r2_hidden(X1,k1_ordinal1(X2))|~r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 2.05/2.23  cnf(c_0_99, plain, (r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_95, c_0_28])).
% 2.05/2.23  cnf(c_0_100, negated_conjecture, (r2_hidden(esk2_3(esk7_0,esk7_0,esk8_0),esk7_0)|r2_hidden(esk8_0,k3_tarski(esk7_0))), inference(spm,[status(thm)],[c_0_96, c_0_57])).
% 2.05/2.23  cnf(c_0_101, negated_conjecture, (r2_hidden(esk8_0,esk2_3(esk7_0,esk7_0,esk8_0))|r2_hidden(X1,k3_tarski(esk7_0))|~r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_52, c_0_97])).
% 2.05/2.23  cnf(c_0_102, negated_conjecture, (v3_ordinal1(esk8_0)), inference(spm,[status(thm)],[c_0_31, c_0_86])).
% 2.05/2.23  cnf(c_0_103, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r1_ordinal1(X1,X2)), inference(rw,[status(thm)],[c_0_98, c_0_40])).
% 2.05/2.23  cnf(c_0_104, negated_conjecture, (r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),esk7_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_99, c_0_20])).
% 2.05/2.23  cnf(c_0_105, negated_conjecture, (r2_hidden(esk8_0,k3_tarski(esk7_0))|r2_hidden(X1,k3_tarski(esk7_0))|~r2_hidden(X1,esk2_3(esk7_0,esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_52, c_0_100])).
% 2.05/2.23  cnf(c_0_106, negated_conjecture, (r2_hidden(esk8_0,esk2_3(esk7_0,esk7_0,esk8_0))|r2_hidden(esk8_0,k3_tarski(esk7_0))), inference(spm,[status(thm)],[c_0_101, c_0_57])).
% 2.05/2.23  cnf(c_0_107, negated_conjecture, (v3_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_62, c_0_102])).
% 2.05/2.23  cnf(c_0_108, plain, (r2_hidden(X1,X2)|X1=X2|~r2_hidden(X1,k1_ordinal1(X2))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 2.05/2.23  cnf(c_0_109, negated_conjecture, (r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))|~r1_ordinal1(X1,esk7_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_103, c_0_20])).
% 2.05/2.23  cnf(c_0_110, negated_conjecture, (r1_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_104, c_0_86])).
% 2.05/2.23  cnf(c_0_111, negated_conjecture, (r2_hidden(esk8_0,k3_tarski(esk7_0))), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 2.05/2.23  cnf(c_0_112, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_28, c_0_107])).
% 2.05/2.23  cnf(c_0_113, plain, (X1=X2|r2_hidden(X1,X2)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_108, c_0_40])).
% 2.05/2.23  cnf(c_0_114, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_107]), c_0_110])])).
% 2.05/2.23  cnf(c_0_115, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk7_0)), inference(spm,[status(thm)],[c_0_69, c_0_111])).
% 2.05/2.23  cnf(c_0_116, negated_conjecture, (r1_ordinal1(X1,esk8_0)|~r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_102]), c_0_112])).
% 2.05/2.23  cnf(c_0_117, negated_conjecture, (k2_xboole_0(esk8_0,k1_tarski(esk8_0))=esk7_0|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_113, c_0_114])).
% 2.05/2.23  cnf(c_0_118, negated_conjecture, (r1_tarski(X1,esk8_0)|~r1_ordinal1(X1,esk8_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_76, c_0_102])).
% 2.05/2.23  cnf(c_0_119, negated_conjecture, (v3_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0))), inference(spm,[status(thm)],[c_0_31, c_0_115])).
% 2.05/2.23  cnf(c_0_120, negated_conjecture, (r1_ordinal1(X1,esk8_0)|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_116, c_0_117])).
% 2.05/2.23  cnf(c_0_121, negated_conjecture, (~r2_hidden(k1_ordinal1(esk8_0),esk7_0)|~v4_ordinal1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.05/2.23  cnf(c_0_122, negated_conjecture, (r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)|~r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_118, c_0_119])).
% 2.05/2.23  cnf(c_0_123, negated_conjecture, (r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_120, c_0_115])).
% 2.05/2.23  cnf(c_0_124, negated_conjecture, (~v4_ordinal1(esk7_0)|~r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(rw,[status(thm)],[c_0_121, c_0_40])).
% 2.05/2.23  cnf(c_0_125, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_122, c_0_123])).
% 2.05/2.23  cnf(c_0_126, negated_conjecture, (r2_hidden(esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0))), inference(spm,[status(thm)],[c_0_83, c_0_111])).
% 2.05/2.23  cnf(c_0_127, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk5_1(esk7_0),esk7_0)|~r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_124, c_0_30])).
% 2.05/2.23  cnf(c_0_128, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_125]), c_0_126])])).
% 2.05/2.23  cnf(c_0_129, negated_conjecture, (r2_hidden(esk5_1(esk7_0),esk7_0)|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_127, c_0_128])])).
% 2.05/2.23  cnf(c_0_130, negated_conjecture, (v3_ordinal1(esk5_1(esk7_0))|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(k3_tarski(esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_31, c_0_129])).
% 2.05/2.23  cnf(c_0_131, negated_conjecture, (v3_ordinal1(k3_tarski(esk7_0))|r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_130]), c_0_31])).
% 2.05/2.23  cnf(c_0_132, negated_conjecture, (k3_tarski(esk7_0)=esk7_0|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(k3_tarski(esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_23, c_0_131])).
% 2.05/2.23  cnf(c_0_133, negated_conjecture, (~v4_ordinal1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_124, c_0_128])])).
% 2.05/2.23  fof(c_0_134, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 2.05/2.23  cnf(c_0_135, negated_conjecture, (r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_132]), c_0_133])).
% 2.05/2.23  cnf(c_0_136, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_134])).
% 2.05/2.23  cnf(c_0_137, negated_conjecture, (r2_hidden(k2_xboole_0(k3_tarski(esk7_0),k1_tarski(k3_tarski(esk7_0))),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_135]), c_0_133])).
% 2.05/2.23  cnf(c_0_138, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_136])).
% 2.05/2.23  cnf(c_0_139, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(X1,k3_tarski(esk7_0))|~r2_hidden(X1,k2_xboole_0(k3_tarski(esk7_0),k1_tarski(k3_tarski(esk7_0))))), inference(spm,[status(thm)],[c_0_52, c_0_137])).
% 2.05/2.23  cnf(c_0_140, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_41, c_0_138])).
% 2.05/2.23  cnf(c_0_141, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_57]), c_0_140])).
% 2.05/2.23  cnf(c_0_142, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_69, c_0_141])).
% 2.05/2.23  cnf(c_0_143, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(spm,[status(thm)],[c_0_74, c_0_142])).
% 2.05/2.23  cnf(c_0_144, negated_conjecture, (v3_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0))), inference(spm,[status(thm)],[c_0_31, c_0_142])).
% 2.05/2.23  cnf(c_0_145, negated_conjecture, (r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_77, c_0_143])).
% 2.05/2.23  cnf(c_0_146, negated_conjecture, (r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_144]), c_0_145])])).
% 2.05/2.23  cnf(c_0_147, negated_conjecture, (r2_hidden(esk7_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0))), inference(spm,[status(thm)],[c_0_83, c_0_141])).
% 2.05/2.23  cnf(c_0_148, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_146]), c_0_147])]), ['proof']).
% 2.05/2.23  # SZS output end CNFRefutation
% 2.05/2.23  # Proof object total steps             : 149
% 2.05/2.23  # Proof object clause steps            : 116
% 2.05/2.23  # Proof object formula steps           : 33
% 2.05/2.23  # Proof object conjectures             : 83
% 2.05/2.23  # Proof object clause conjectures      : 80
% 2.05/2.23  # Proof object formula conjectures     : 3
% 2.05/2.23  # Proof object initial clauses used    : 26
% 2.05/2.23  # Proof object initial formulas used   : 16
% 2.05/2.23  # Proof object generating inferences   : 73
% 2.05/2.23  # Proof object simplifying inferences  : 40
% 2.05/2.23  # Training examples: 0 positive, 0 negative
% 2.05/2.23  # Parsed axioms                        : 18
% 2.05/2.23  # Removed by relevancy pruning/SinE    : 0
% 2.05/2.23  # Initial clauses                      : 39
% 2.05/2.23  # Removed in clause preprocessing      : 1
% 2.05/2.23  # Initial clauses in saturation        : 38
% 2.05/2.23  # Processed clauses                    : 4477
% 2.05/2.23  # ...of these trivial                  : 137
% 2.05/2.23  # ...subsumed                          : 1623
% 2.05/2.23  # ...remaining for further processing  : 2717
% 2.05/2.23  # Other redundant clauses eliminated   : 25
% 2.05/2.23  # Clauses deleted for lack of memory   : 0
% 2.05/2.23  # Backward-subsumed                    : 235
% 2.05/2.23  # Backward-rewritten                   : 407
% 2.05/2.23  # Generated clauses                    : 208644
% 2.05/2.23  # ...of the previous two non-trivial   : 197702
% 2.05/2.23  # Contextual simplify-reflections      : 46
% 2.05/2.23  # Paramodulations                      : 208609
% 2.05/2.23  # Factorizations                       : 0
% 2.05/2.23  # Equation resolutions                 : 25
% 2.05/2.23  # Propositional unsat checks           : 0
% 2.05/2.23  #    Propositional check models        : 0
% 2.05/2.23  #    Propositional check unsatisfiable : 0
% 2.05/2.23  #    Propositional clauses             : 0
% 2.05/2.23  #    Propositional clauses after purity: 0
% 2.05/2.23  #    Propositional unsat core size     : 0
% 2.05/2.23  #    Propositional preprocessing time  : 0.000
% 2.05/2.23  #    Propositional encoding time       : 0.000
% 2.05/2.23  #    Propositional solver time         : 0.000
% 2.05/2.23  #    Success case prop preproc time    : 0.000
% 2.05/2.23  #    Success case prop encoding time   : 0.000
% 2.05/2.23  #    Success case prop solver time     : 0.000
% 2.05/2.23  # Current number of processed clauses  : 2023
% 2.05/2.23  #    Positive orientable unit clauses  : 418
% 2.05/2.23  #    Positive unorientable unit clauses: 0
% 2.05/2.23  #    Negative unit clauses             : 82
% 2.05/2.23  #    Non-unit-clauses                  : 1523
% 2.05/2.23  # Current number of unprocessed clauses: 192751
% 2.05/2.23  # ...number of literals in the above   : 936176
% 2.05/2.23  # Current number of archived formulas  : 0
% 2.05/2.23  # Current number of archived clauses   : 689
% 2.05/2.23  # Clause-clause subsumption calls (NU) : 229512
% 2.05/2.23  # Rec. Clause-clause subsumption calls : 127797
% 2.05/2.23  # Non-unit clause-clause subsumptions  : 1400
% 2.05/2.23  # Unit Clause-clause subsumption calls : 33784
% 2.05/2.23  # Rewrite failures with RHS unbound    : 0
% 2.05/2.23  # BW rewrite match attempts            : 502
% 2.05/2.23  # BW rewrite match successes           : 60
% 2.05/2.23  # Condensation attempts                : 0
% 2.05/2.23  # Condensation successes               : 0
% 2.05/2.23  # Termbank termtop insertions          : 5247427
% 2.05/2.24  
% 2.05/2.24  # -------------------------------------------------
% 2.05/2.24  # User time                : 1.808 s
% 2.05/2.24  # System time              : 0.091 s
% 2.05/2.24  # Total time               : 1.900 s
% 2.05/2.24  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
