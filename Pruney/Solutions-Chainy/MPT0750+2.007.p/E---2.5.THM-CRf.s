%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:33 EST 2020

% Result     : Theorem 6.25s
% Output     : CNFRefutation 6.25s
% Verified   : 
% Statistics : Number of formulae       :  172 (349022 expanded)
%              Number of clauses        :  139 (156015 expanded)
%              Number of leaves         :   16 (82043 expanded)
%              Depth                    :   56
%              Number of atoms          :  472 (1420517 expanded)
%              Number of equality atoms :   38 (115338 expanded)
%              Maximal formula depth    :   17 (   3 average)
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

fof(connectedness_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
        | r1_ordinal1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

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
    ! [X36,X37] :
      ( ~ v3_ordinal1(X36)
      | ~ v3_ordinal1(X37)
      | r2_hidden(X36,X37)
      | X36 = X37
      | r2_hidden(X37,X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

fof(c_0_18,negated_conjecture,(
    ! [X49] :
      ( v3_ordinal1(esk7_0)
      & ( v3_ordinal1(esk8_0)
        | ~ v4_ordinal1(esk7_0) )
      & ( r2_hidden(esk8_0,esk7_0)
        | ~ v4_ordinal1(esk7_0) )
      & ( ~ r2_hidden(k1_ordinal1(esk8_0),esk7_0)
        | ~ v4_ordinal1(esk7_0) )
      & ( v4_ordinal1(esk7_0)
        | ~ v3_ordinal1(X49)
        | ~ r2_hidden(X49,esk7_0)
        | r2_hidden(k1_ordinal1(X49),esk7_0) ) ) ),
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
    ! [X41] :
      ( ( r2_hidden(esk5_1(X41),X41)
        | v3_ordinal1(k3_tarski(X41)) )
      & ( ~ v3_ordinal1(esk5_1(X41))
        | v3_ordinal1(k3_tarski(X41)) ) ) ),
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
    ! [X34,X35] :
      ( ~ v3_ordinal1(X35)
      | ~ r2_hidden(X34,X35)
      | v3_ordinal1(X34) ) ),
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
    ! [X45,X46] :
      ( ~ r2_hidden(X45,X46)
      | ~ r1_tarski(X46,X45) ) ),
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
    ! [X38] :
      ( ~ v3_ordinal1(X38)
      | v3_ordinal1(k1_ordinal1(X38)) ) ),
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

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | r2_hidden(esk2_3(esk7_0,esk7_0,X1),esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_89])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,esk7_0,esk8_0),esk7_0)
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_86])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | r2_hidden(X1,esk2_3(esk7_0,esk7_0,X1))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_89])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,esk7_0,esk8_0),esk7_0)
    | r2_hidden(X1,k3_tarski(esk7_0))
    | ~ r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_91])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(esk8_0,esk2_3(esk7_0,esk7_0,esk8_0))
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_86])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,esk7_0,esk8_0),esk7_0)
    | r2_hidden(esk8_0,k3_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_57])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(esk8_0,esk2_3(esk7_0,esk7_0,esk8_0))
    | r2_hidden(X1,k3_tarski(esk7_0))
    | ~ r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_94])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(esk8_0,k3_tarski(esk7_0))
    | r2_hidden(X1,k3_tarski(esk7_0))
    | ~ r2_hidden(X1,esk2_3(esk7_0,esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_95])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(esk8_0,esk2_3(esk7_0,esk7_0,esk8_0))
    | r2_hidden(esk8_0,k3_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_57])).

cnf(c_0_99,negated_conjecture,
    ( v3_ordinal1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_86])).

cnf(c_0_100,negated_conjecture,
    ( r2_hidden(esk8_0,k3_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_101,negated_conjecture,
    ( v3_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_99])).

cnf(c_0_102,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_103,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_100])).

cnf(c_0_104,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_101])).

cnf(c_0_105,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_102,c_0_42])).

cnf(c_0_106,negated_conjecture,
    ( r1_tarski(X1,esk8_0)
    | ~ r1_ordinal1(X1,esk8_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_99])).

cnf(c_0_107,negated_conjecture,
    ( v3_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_103])).

cnf(c_0_108,negated_conjecture,
    ( r1_ordinal1(X1,esk8_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_99]),c_0_104])).

cnf(c_0_109,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),X1)
    | r2_hidden(esk1_2(esk7_0,X1),esk7_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_103])).

fof(c_0_110,plain,(
    ! [X24,X25] :
      ( ~ v3_ordinal1(X24)
      | ~ v3_ordinal1(X25)
      | r1_ordinal1(X24,X25)
      | r1_ordinal1(X25,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).

cnf(c_0_111,negated_conjecture,
    ( r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)
    | ~ r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_112,negated_conjecture,
    ( r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)
    | r2_hidden(esk1_2(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0))),esk7_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_113,plain,
    ( r1_ordinal1(X1,X2)
    | r1_ordinal1(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_110])).

cnf(c_0_114,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_115,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0))),esk7_0)
    | r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_111,c_0_112])).

cnf(c_0_116,negated_conjecture,
    ( r2_hidden(esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_100])).

cnf(c_0_117,negated_conjecture,
    ( r1_ordinal1(X1,esk7_0)
    | r1_ordinal1(esk7_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_113,c_0_20])).

cnf(c_0_118,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r1_ordinal1(X1,X2) ),
    inference(rw,[status(thm)],[c_0_114,c_0_40])).

cnf(c_0_119,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0))),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_115]),c_0_116])])).

cnf(c_0_120,negated_conjecture,
    ( k2_xboole_0(esk8_0,k1_tarski(esk8_0)) = esk7_0
    | r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_101])).

cnf(c_0_121,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | ~ r1_ordinal1(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_101])).

cnf(c_0_122,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | ~ r1_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_101])).

cnf(c_0_123,negated_conjecture,
    ( r1_ordinal1(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | r1_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_117,c_0_101])).

cnf(c_0_124,negated_conjecture,
    ( r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | ~ r1_ordinal1(X1,esk8_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_118,c_0_99])).

cnf(c_0_125,negated_conjecture,
    ( v3_ordinal1(esk1_2(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_119])).

cnf(c_0_126,negated_conjecture,
    ( r1_ordinal1(X1,esk8_0)
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_120])).

cnf(c_0_127,negated_conjecture,
    ( r1_tarski(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | ~ r1_ordinal1(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_121,c_0_20])).

cnf(c_0_128,negated_conjecture,
    ( r1_ordinal1(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | r1_tarski(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_122,c_0_123])).

cnf(c_0_129,negated_conjecture,
    ( r1_ordinal1(X1,esk8_0)
    | r1_ordinal1(esk8_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_113,c_0_99])).

cnf(c_0_130,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0))),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | ~ r1_ordinal1(esk1_2(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0))),esk8_0) ),
    inference(spm,[status(thm)],[c_0_124,c_0_125])).

cnf(c_0_131,negated_conjecture,
    ( r1_ordinal1(esk1_2(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0))),esk8_0)
    | r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_126,c_0_119])).

cnf(c_0_132,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | r1_tarski(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_127,c_0_128])).

cnf(c_0_133,negated_conjecture,
    ( r1_tarski(X1,esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0))
    | ~ r1_ordinal1(X1,esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_107])).

cnf(c_0_134,negated_conjecture,
    ( r1_ordinal1(esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0))
    | r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_129,c_0_107])).

cnf(c_0_135,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0))),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_130,c_0_131])).

cnf(c_0_136,negated_conjecture,
    ( r1_tarski(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | ~ r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_132])).

cnf(c_0_137,negated_conjecture,
    ( r1_tarski(esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0))
    | ~ r1_ordinal1(esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_133,c_0_99])).

cnf(c_0_138,negated_conjecture,
    ( r1_ordinal1(esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0))
    | r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_111,c_0_134])).

cnf(c_0_139,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | r1_tarski(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_135]),c_0_136])).

cnf(c_0_140,negated_conjecture,
    ( r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)
    | r1_tarski(esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_137,c_0_138])).

fof(c_0_141,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_142,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | ~ r2_hidden(X1,k1_ordinal1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_143,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_139])).

cnf(c_0_144,negated_conjecture,
    ( r1_tarski(esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_140]),c_0_116])])).

cnf(c_0_145,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_141])).

cnf(c_0_146,negated_conjecture,
    ( ~ r2_hidden(k1_ordinal1(esk8_0),esk7_0)
    | ~ v4_ordinal1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_147,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_142,c_0_40])).

cnf(c_0_148,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_143,c_0_103])).

cnf(c_0_149,negated_conjecture,
    ( ~ r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_144])).

cnf(c_0_150,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_145])).

cnf(c_0_151,negated_conjecture,
    ( ~ v4_ordinal1(esk7_0)
    | ~ r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(rw,[status(thm)],[c_0_146,c_0_40])).

cnf(c_0_152,negated_conjecture,
    ( esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0) = esk8_0
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_148]),c_0_149])).

cnf(c_0_153,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_150])).

cnf(c_0_154,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk5_1(esk7_0),esk7_0)
    | ~ r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_151,c_0_30])).

cnf(c_0_155,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_152]),c_0_153])).

cnf(c_0_156,negated_conjecture,
    ( r2_hidden(esk5_1(esk7_0),esk7_0)
    | r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_154,c_0_155])])).

cnf(c_0_157,negated_conjecture,
    ( v3_ordinal1(esk5_1(esk7_0))
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(k3_tarski(esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_156])).

cnf(c_0_158,negated_conjecture,
    ( v3_ordinal1(k3_tarski(esk7_0))
    | r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_157]),c_0_31])).

cnf(c_0_159,negated_conjecture,
    ( k3_tarski(esk7_0) = esk7_0
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(k3_tarski(esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_158])).

cnf(c_0_160,negated_conjecture,
    ( ~ v4_ordinal1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_151,c_0_155])])).

cnf(c_0_161,negated_conjecture,
    ( r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_159]),c_0_160])).

cnf(c_0_162,negated_conjecture,
    ( r2_hidden(k2_xboole_0(k3_tarski(esk7_0),k1_tarski(k3_tarski(esk7_0))),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_161]),c_0_160])).

cnf(c_0_163,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(X1,k3_tarski(esk7_0))
    | ~ r2_hidden(X1,k2_xboole_0(k3_tarski(esk7_0),k1_tarski(k3_tarski(esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_162])).

cnf(c_0_164,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_163,c_0_57]),c_0_153])).

cnf(c_0_165,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_164])).

cnf(c_0_166,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_165])).

cnf(c_0_167,negated_conjecture,
    ( v3_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_165])).

cnf(c_0_168,negated_conjecture,
    ( r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_166])).

cnf(c_0_169,negated_conjecture,
    ( r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_167]),c_0_168])])).

cnf(c_0_170,negated_conjecture,
    ( r2_hidden(esk7_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_164])).

cnf(c_0_171,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_169]),c_0_170])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:50:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 6.25/6.44  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 6.25/6.44  # and selection function SelectCQIArEqFirst.
% 6.25/6.44  #
% 6.25/6.44  # Preprocessing time       : 0.029 s
% 6.25/6.44  # Presaturation interreduction done
% 6.25/6.44  
% 6.25/6.44  # Proof found!
% 6.25/6.44  # SZS status Theorem
% 6.25/6.44  # SZS output start CNFRefutation
% 6.25/6.44  fof(t41_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_ordinal1)).
% 6.25/6.44  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 6.25/6.44  fof(t35_ordinal1, axiom, ![X1]:(![X2]:(r2_hidden(X2,X1)=>v3_ordinal1(X2))=>v3_ordinal1(k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_ordinal1)).
% 6.25/6.44  fof(d6_ordinal1, axiom, ![X1]:(v4_ordinal1(X1)<=>X1=k3_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_ordinal1)).
% 6.25/6.44  fof(t23_ordinal1, axiom, ![X1, X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>v3_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 6.25/6.44  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 6.25/6.44  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.25/6.44  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.25/6.44  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 6.25/6.44  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 6.25/6.44  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 6.25/6.44  fof(t34_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 6.25/6.44  fof(t13_ordinal1, axiom, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 6.25/6.44  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 6.25/6.44  fof(connectedness_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 6.25/6.44  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.25/6.44  fof(c_0_16, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1)))))), inference(assume_negation,[status(cth)],[t41_ordinal1])).
% 6.25/6.44  fof(c_0_17, plain, ![X36, X37]:(~v3_ordinal1(X36)|(~v3_ordinal1(X37)|(r2_hidden(X36,X37)|X36=X37|r2_hidden(X37,X36)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 6.25/6.44  fof(c_0_18, negated_conjecture, ![X49]:(v3_ordinal1(esk7_0)&(((v3_ordinal1(esk8_0)|~v4_ordinal1(esk7_0))&((r2_hidden(esk8_0,esk7_0)|~v4_ordinal1(esk7_0))&(~r2_hidden(k1_ordinal1(esk8_0),esk7_0)|~v4_ordinal1(esk7_0))))&(v4_ordinal1(esk7_0)|(~v3_ordinal1(X49)|(~r2_hidden(X49,esk7_0)|r2_hidden(k1_ordinal1(X49),esk7_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])])])).
% 6.25/6.44  cnf(c_0_19, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 6.25/6.44  cnf(c_0_20, negated_conjecture, (v3_ordinal1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 6.25/6.44  fof(c_0_21, plain, ![X41]:((r2_hidden(esk5_1(X41),X41)|v3_ordinal1(k3_tarski(X41)))&(~v3_ordinal1(esk5_1(X41))|v3_ordinal1(k3_tarski(X41)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_ordinal1])])])])).
% 6.25/6.44  fof(c_0_22, plain, ![X27]:((~v4_ordinal1(X27)|X27=k3_tarski(X27))&(X27!=k3_tarski(X27)|v4_ordinal1(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_ordinal1])])).
% 6.25/6.44  cnf(c_0_23, negated_conjecture, (X1=esk7_0|r2_hidden(X1,esk7_0)|r2_hidden(esk7_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 6.25/6.44  cnf(c_0_24, plain, (r2_hidden(esk5_1(X1),X1)|v3_ordinal1(k3_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 6.25/6.44  fof(c_0_25, plain, ![X34, X35]:(~v3_ordinal1(X35)|(~r2_hidden(X34,X35)|v3_ordinal1(X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).
% 6.25/6.44  cnf(c_0_26, plain, (v4_ordinal1(X1)|X1!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 6.25/6.44  cnf(c_0_27, negated_conjecture, (k3_tarski(X1)=esk7_0|r2_hidden(esk7_0,k3_tarski(X1))|r2_hidden(k3_tarski(X1),esk7_0)|r2_hidden(esk5_1(X1),X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 6.25/6.44  cnf(c_0_28, plain, (v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 6.25/6.44  cnf(c_0_29, negated_conjecture, (r2_hidden(esk8_0,esk7_0)|~v4_ordinal1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 6.25/6.44  cnf(c_0_30, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(esk5_1(esk7_0),esk7_0)|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27])])).
% 6.25/6.44  cnf(c_0_31, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_28, c_0_20])).
% 6.25/6.44  cnf(c_0_32, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk5_1(esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 6.25/6.44  cnf(c_0_33, plain, (v3_ordinal1(k3_tarski(X1))|~v3_ordinal1(esk5_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 6.25/6.44  cnf(c_0_34, negated_conjecture, (v3_ordinal1(esk5_1(esk7_0))|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 6.25/6.44  fof(c_0_35, plain, ![X26]:k1_ordinal1(X26)=k2_xboole_0(X26,k1_tarski(X26)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 6.25/6.44  fof(c_0_36, plain, ![X45, X46]:(~r2_hidden(X45,X46)|~r1_tarski(X46,X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 6.25/6.44  fof(c_0_37, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 6.25/6.44  cnf(c_0_38, negated_conjecture, (v3_ordinal1(k3_tarski(esk7_0))|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_31])).
% 6.25/6.44  cnf(c_0_39, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(k1_ordinal1(X1),esk7_0)|~v3_ordinal1(X1)|~r2_hidden(X1,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 6.25/6.44  cnf(c_0_40, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 6.25/6.44  cnf(c_0_41, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 6.25/6.44  cnf(c_0_42, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 6.25/6.44  cnf(c_0_43, negated_conjecture, (k3_tarski(esk7_0)=esk7_0|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_23, c_0_38])).
% 6.25/6.44  fof(c_0_44, plain, ![X13, X14, X15, X17, X18, X19, X20, X22]:((((r2_hidden(X15,esk2_3(X13,X14,X15))|~r2_hidden(X15,X14)|X14!=k3_tarski(X13))&(r2_hidden(esk2_3(X13,X14,X15),X13)|~r2_hidden(X15,X14)|X14!=k3_tarski(X13)))&(~r2_hidden(X17,X18)|~r2_hidden(X18,X13)|r2_hidden(X17,X14)|X14!=k3_tarski(X13)))&((~r2_hidden(esk3_2(X19,X20),X20)|(~r2_hidden(esk3_2(X19,X20),X22)|~r2_hidden(X22,X19))|X20=k3_tarski(X19))&((r2_hidden(esk3_2(X19,X20),esk4_2(X19,X20))|r2_hidden(esk3_2(X19,X20),X20)|X20=k3_tarski(X19))&(r2_hidden(esk4_2(X19,X20),X19)|r2_hidden(esk3_2(X19,X20),X20)|X20=k3_tarski(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 6.25/6.44  cnf(c_0_45, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk7_0)|~v3_ordinal1(X1)|~r2_hidden(X1,esk7_0)), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 6.25/6.44  cnf(c_0_46, plain, (r2_hidden(esk1_2(X1,X2),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 6.25/6.44  cnf(c_0_47, negated_conjecture, (r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_43]), c_0_29])).
% 6.25/6.44  cnf(c_0_48, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 6.25/6.44  cnf(c_0_49, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk7_0)|~r2_hidden(X1,esk7_0)), inference(csr,[status(thm)],[c_0_45, c_0_31])).
% 6.25/6.44  cnf(c_0_50, negated_conjecture, (r2_hidden(esk1_2(esk7_0,k3_tarski(esk7_0)),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 6.25/6.44  fof(c_0_51, plain, ![X30]:r2_hidden(X30,k1_ordinal1(X30)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 6.25/6.44  cnf(c_0_52, plain, (r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X3,X2)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_48])).
% 6.25/6.44  cnf(c_0_53, negated_conjecture, (r2_hidden(k2_xboole_0(esk1_2(esk7_0,k3_tarski(esk7_0)),k1_tarski(esk1_2(esk7_0,k3_tarski(esk7_0)))),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_29])).
% 6.25/6.44  cnf(c_0_54, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 6.25/6.44  fof(c_0_55, plain, ![X38]:(~v3_ordinal1(X38)|v3_ordinal1(k1_ordinal1(X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 6.25/6.44  cnf(c_0_56, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(X1,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)|~r2_hidden(X1,k2_xboole_0(esk1_2(esk7_0,k3_tarski(esk7_0)),k1_tarski(esk1_2(esk7_0,k3_tarski(esk7_0)))))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 6.25/6.44  cnf(c_0_57, plain, (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_54, c_0_40])).
% 6.25/6.44  cnf(c_0_58, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 6.25/6.44  cnf(c_0_59, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 6.25/6.44  cnf(c_0_60, negated_conjecture, (r2_hidden(esk1_2(esk7_0,k3_tarski(esk7_0)),k3_tarski(esk7_0))|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 6.25/6.44  fof(c_0_61, plain, ![X39, X40]:((~r2_hidden(X39,k1_ordinal1(X40))|r1_ordinal1(X39,X40)|~v3_ordinal1(X40)|~v3_ordinal1(X39))&(~r1_ordinal1(X39,X40)|r2_hidden(X39,k1_ordinal1(X40))|~v3_ordinal1(X40)|~v3_ordinal1(X39))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).
% 6.25/6.44  cnf(c_0_62, plain, (v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_58, c_0_40])).
% 6.25/6.44  fof(c_0_63, plain, ![X31, X32]:((~r2_hidden(X31,k1_ordinal1(X32))|(r2_hidden(X31,X32)|X31=X32))&((~r2_hidden(X31,X32)|r2_hidden(X31,k1_ordinal1(X32)))&(X31!=X32|r2_hidden(X31,k1_ordinal1(X32))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).
% 6.25/6.44  cnf(c_0_64, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|X2!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 6.25/6.44  cnf(c_0_65, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)|r1_tarski(esk7_0,k3_tarski(esk7_0))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 6.25/6.44  cnf(c_0_66, plain, (r1_ordinal1(X1,X2)|~r2_hidden(X1,k1_ordinal1(X2))|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 6.25/6.44  cnf(c_0_67, negated_conjecture, (v3_ordinal1(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(spm,[status(thm)],[c_0_62, c_0_20])).
% 6.25/6.44  cnf(c_0_68, plain, (r2_hidden(X1,k1_ordinal1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 6.25/6.44  cnf(c_0_69, plain, (r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)|~r2_hidden(X2,k3_tarski(X1))), inference(er,[status(thm)],[c_0_64])).
% 6.25/6.44  cnf(c_0_70, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_65]), c_0_47])).
% 6.25/6.44  fof(c_0_71, plain, ![X28, X29]:((~r1_ordinal1(X28,X29)|r1_tarski(X28,X29)|(~v3_ordinal1(X28)|~v3_ordinal1(X29)))&(~r1_tarski(X28,X29)|r1_ordinal1(X28,X29)|(~v3_ordinal1(X28)|~v3_ordinal1(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 6.25/6.44  cnf(c_0_72, plain, (r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_66, c_0_40])).
% 6.25/6.44  cnf(c_0_73, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(spm,[status(thm)],[c_0_28, c_0_67])).
% 6.25/6.44  cnf(c_0_74, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_68, c_0_40])).
% 6.25/6.44  cnf(c_0_75, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 6.25/6.44  cnf(c_0_76, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 6.25/6.44  cnf(c_0_77, negated_conjecture, (r1_ordinal1(X1,esk7_0)|~r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_20]), c_0_73])).
% 6.25/6.44  cnf(c_0_78, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 6.25/6.44  cnf(c_0_79, plain, (r2_hidden(X1,esk2_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k3_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 6.25/6.44  cnf(c_0_80, negated_conjecture, (r1_tarski(X1,esk7_0)|~r1_ordinal1(X1,esk7_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_76, c_0_20])).
% 6.25/6.44  cnf(c_0_81, negated_conjecture, (v3_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_31, c_0_75])).
% 6.25/6.44  cnf(c_0_82, negated_conjecture, (r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 6.25/6.44  cnf(c_0_83, plain, (r2_hidden(X1,esk2_3(X2,k3_tarski(X2),X1))|~r2_hidden(X1,k3_tarski(X2))), inference(er,[status(thm)],[c_0_79])).
% 6.25/6.44  cnf(c_0_84, negated_conjecture, (r2_hidden(esk8_0,esk7_0)|r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82])).
% 6.25/6.44  cnf(c_0_85, negated_conjecture, (r2_hidden(esk7_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_83, c_0_70])).
% 6.25/6.44  cnf(c_0_86, negated_conjecture, (r2_hidden(esk8_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_84]), c_0_85])).
% 6.25/6.44  cnf(c_0_87, plain, (X1=k3_tarski(X1)|~v4_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 6.25/6.44  cnf(c_0_88, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_49, c_0_86])).
% 6.25/6.44  cnf(c_0_89, negated_conjecture, (k3_tarski(esk7_0)=esk7_0|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 6.25/6.44  cnf(c_0_90, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|r2_hidden(esk2_3(esk7_0,esk7_0,X1),esk7_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_69, c_0_89])).
% 6.25/6.44  cnf(c_0_91, negated_conjecture, (r2_hidden(esk2_3(esk7_0,esk7_0,esk8_0),esk7_0)|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_90, c_0_86])).
% 6.25/6.44  cnf(c_0_92, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|r2_hidden(X1,esk2_3(esk7_0,esk7_0,X1))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_83, c_0_89])).
% 6.25/6.44  cnf(c_0_93, negated_conjecture, (r2_hidden(esk2_3(esk7_0,esk7_0,esk8_0),esk7_0)|r2_hidden(X1,k3_tarski(esk7_0))|~r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_52, c_0_91])).
% 6.25/6.44  cnf(c_0_94, negated_conjecture, (r2_hidden(esk8_0,esk2_3(esk7_0,esk7_0,esk8_0))|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_92, c_0_86])).
% 6.25/6.44  cnf(c_0_95, negated_conjecture, (r2_hidden(esk2_3(esk7_0,esk7_0,esk8_0),esk7_0)|r2_hidden(esk8_0,k3_tarski(esk7_0))), inference(spm,[status(thm)],[c_0_93, c_0_57])).
% 6.25/6.44  cnf(c_0_96, negated_conjecture, (r2_hidden(esk8_0,esk2_3(esk7_0,esk7_0,esk8_0))|r2_hidden(X1,k3_tarski(esk7_0))|~r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_52, c_0_94])).
% 6.25/6.44  cnf(c_0_97, negated_conjecture, (r2_hidden(esk8_0,k3_tarski(esk7_0))|r2_hidden(X1,k3_tarski(esk7_0))|~r2_hidden(X1,esk2_3(esk7_0,esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_52, c_0_95])).
% 6.25/6.44  cnf(c_0_98, negated_conjecture, (r2_hidden(esk8_0,esk2_3(esk7_0,esk7_0,esk8_0))|r2_hidden(esk8_0,k3_tarski(esk7_0))), inference(spm,[status(thm)],[c_0_96, c_0_57])).
% 6.25/6.44  cnf(c_0_99, negated_conjecture, (v3_ordinal1(esk8_0)), inference(spm,[status(thm)],[c_0_31, c_0_86])).
% 6.25/6.44  cnf(c_0_100, negated_conjecture, (r2_hidden(esk8_0,k3_tarski(esk7_0))), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 6.25/6.44  cnf(c_0_101, negated_conjecture, (v3_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_62, c_0_99])).
% 6.25/6.44  cnf(c_0_102, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 6.25/6.44  cnf(c_0_103, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk7_0)), inference(spm,[status(thm)],[c_0_69, c_0_100])).
% 6.25/6.44  cnf(c_0_104, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_28, c_0_101])).
% 6.25/6.44  cnf(c_0_105, plain, (r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_102, c_0_42])).
% 6.25/6.44  cnf(c_0_106, negated_conjecture, (r1_tarski(X1,esk8_0)|~r1_ordinal1(X1,esk8_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_76, c_0_99])).
% 6.25/6.44  cnf(c_0_107, negated_conjecture, (v3_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0))), inference(spm,[status(thm)],[c_0_31, c_0_103])).
% 6.25/6.44  cnf(c_0_108, negated_conjecture, (r1_ordinal1(X1,esk8_0)|~r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_99]), c_0_104])).
% 6.25/6.44  cnf(c_0_109, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),X1)|r2_hidden(esk1_2(esk7_0,X1),esk7_0)), inference(spm,[status(thm)],[c_0_105, c_0_103])).
% 6.25/6.44  fof(c_0_110, plain, ![X24, X25]:(~v3_ordinal1(X24)|~v3_ordinal1(X25)|(r1_ordinal1(X24,X25)|r1_ordinal1(X25,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).
% 6.25/6.44  cnf(c_0_111, negated_conjecture, (r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)|~r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 6.25/6.44  cnf(c_0_112, negated_conjecture, (r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)|r2_hidden(esk1_2(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0))),esk7_0)), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 6.25/6.44  cnf(c_0_113, plain, (r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_110])).
% 6.25/6.44  cnf(c_0_114, plain, (r2_hidden(X1,k1_ordinal1(X2))|~r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 6.25/6.44  cnf(c_0_115, negated_conjecture, (r2_hidden(esk1_2(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0))),esk7_0)|r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_111, c_0_112])).
% 6.25/6.44  cnf(c_0_116, negated_conjecture, (r2_hidden(esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0))), inference(spm,[status(thm)],[c_0_83, c_0_100])).
% 6.25/6.44  cnf(c_0_117, negated_conjecture, (r1_ordinal1(X1,esk7_0)|r1_ordinal1(esk7_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_113, c_0_20])).
% 6.25/6.44  cnf(c_0_118, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r1_ordinal1(X1,X2)), inference(rw,[status(thm)],[c_0_114, c_0_40])).
% 6.25/6.44  cnf(c_0_119, negated_conjecture, (r2_hidden(esk1_2(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0))),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_115]), c_0_116])])).
% 6.25/6.44  cnf(c_0_120, negated_conjecture, (k2_xboole_0(esk8_0,k1_tarski(esk8_0))=esk7_0|r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_23, c_0_101])).
% 6.25/6.44  cnf(c_0_121, negated_conjecture, (r1_tarski(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|~r1_ordinal1(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_76, c_0_101])).
% 6.25/6.44  cnf(c_0_122, negated_conjecture, (r1_tarski(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|~r1_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_80, c_0_101])).
% 6.25/6.44  cnf(c_0_123, negated_conjecture, (r1_ordinal1(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|r1_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_117, c_0_101])).
% 6.25/6.44  cnf(c_0_124, negated_conjecture, (r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|~r1_ordinal1(X1,esk8_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_118, c_0_99])).
% 6.25/6.44  cnf(c_0_125, negated_conjecture, (v3_ordinal1(esk1_2(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0))))), inference(spm,[status(thm)],[c_0_31, c_0_119])).
% 6.25/6.44  cnf(c_0_126, negated_conjecture, (r1_ordinal1(X1,esk8_0)|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_108, c_0_120])).
% 6.25/6.44  cnf(c_0_127, negated_conjecture, (r1_tarski(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|~r1_ordinal1(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_121, c_0_20])).
% 6.25/6.44  cnf(c_0_128, negated_conjecture, (r1_ordinal1(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|r1_tarski(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_122, c_0_123])).
% 6.25/6.44  cnf(c_0_129, negated_conjecture, (r1_ordinal1(X1,esk8_0)|r1_ordinal1(esk8_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_113, c_0_99])).
% 6.25/6.44  cnf(c_0_130, negated_conjecture, (r2_hidden(esk1_2(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0))),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|~r1_ordinal1(esk1_2(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0))),esk8_0)), inference(spm,[status(thm)],[c_0_124, c_0_125])).
% 6.25/6.44  cnf(c_0_131, negated_conjecture, (r1_ordinal1(esk1_2(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0))),esk8_0)|r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_126, c_0_119])).
% 6.25/6.44  cnf(c_0_132, negated_conjecture, (r1_tarski(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|r1_tarski(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_127, c_0_128])).
% 6.25/6.44  cnf(c_0_133, negated_conjecture, (r1_tarski(X1,esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0))|~r1_ordinal1(X1,esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_76, c_0_107])).
% 6.25/6.44  cnf(c_0_134, negated_conjecture, (r1_ordinal1(esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0))|r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_129, c_0_107])).
% 6.25/6.44  cnf(c_0_135, negated_conjecture, (r2_hidden(esk1_2(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0))),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_130, c_0_131])).
% 6.25/6.44  cnf(c_0_136, negated_conjecture, (r1_tarski(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|~r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_41, c_0_132])).
% 6.25/6.44  cnf(c_0_137, negated_conjecture, (r1_tarski(esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0))|~r1_ordinal1(esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0))), inference(spm,[status(thm)],[c_0_133, c_0_99])).
% 6.25/6.44  cnf(c_0_138, negated_conjecture, (r1_ordinal1(esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0))|r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_111, c_0_134])).
% 6.25/6.44  cnf(c_0_139, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|r1_tarski(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_135]), c_0_136])).
% 6.25/6.44  cnf(c_0_140, negated_conjecture, (r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)|r1_tarski(esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0))), inference(spm,[status(thm)],[c_0_137, c_0_138])).
% 6.25/6.44  fof(c_0_141, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 6.25/6.44  cnf(c_0_142, plain, (r2_hidden(X1,X2)|X1=X2|~r2_hidden(X1,k1_ordinal1(X2))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 6.25/6.44  cnf(c_0_143, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_102, c_0_139])).
% 6.25/6.44  cnf(c_0_144, negated_conjecture, (r1_tarski(esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_140]), c_0_116])])).
% 6.25/6.44  cnf(c_0_145, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_141])).
% 6.25/6.44  cnf(c_0_146, negated_conjecture, (~r2_hidden(k1_ordinal1(esk8_0),esk7_0)|~v4_ordinal1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 6.25/6.44  cnf(c_0_147, plain, (X1=X2|r2_hidden(X1,X2)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_142, c_0_40])).
% 6.25/6.44  cnf(c_0_148, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_143, c_0_103])).
% 6.25/6.44  cnf(c_0_149, negated_conjecture, (~r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_41, c_0_144])).
% 6.25/6.44  cnf(c_0_150, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_145])).
% 6.25/6.44  cnf(c_0_151, negated_conjecture, (~v4_ordinal1(esk7_0)|~r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(rw,[status(thm)],[c_0_146, c_0_40])).
% 6.25/6.44  cnf(c_0_152, negated_conjecture, (esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0)=esk8_0|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_147, c_0_148]), c_0_149])).
% 6.25/6.44  cnf(c_0_153, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_41, c_0_150])).
% 6.25/6.44  cnf(c_0_154, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk5_1(esk7_0),esk7_0)|~r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_151, c_0_30])).
% 6.25/6.44  cnf(c_0_155, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_152]), c_0_153])).
% 6.25/6.44  cnf(c_0_156, negated_conjecture, (r2_hidden(esk5_1(esk7_0),esk7_0)|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_154, c_0_155])])).
% 6.25/6.44  cnf(c_0_157, negated_conjecture, (v3_ordinal1(esk5_1(esk7_0))|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(k3_tarski(esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_31, c_0_156])).
% 6.25/6.44  cnf(c_0_158, negated_conjecture, (v3_ordinal1(k3_tarski(esk7_0))|r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_157]), c_0_31])).
% 6.25/6.44  cnf(c_0_159, negated_conjecture, (k3_tarski(esk7_0)=esk7_0|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(k3_tarski(esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_23, c_0_158])).
% 6.25/6.44  cnf(c_0_160, negated_conjecture, (~v4_ordinal1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_151, c_0_155])])).
% 6.25/6.44  cnf(c_0_161, negated_conjecture, (r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_159]), c_0_160])).
% 6.25/6.44  cnf(c_0_162, negated_conjecture, (r2_hidden(k2_xboole_0(k3_tarski(esk7_0),k1_tarski(k3_tarski(esk7_0))),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_161]), c_0_160])).
% 6.25/6.44  cnf(c_0_163, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(X1,k3_tarski(esk7_0))|~r2_hidden(X1,k2_xboole_0(k3_tarski(esk7_0),k1_tarski(k3_tarski(esk7_0))))), inference(spm,[status(thm)],[c_0_52, c_0_162])).
% 6.25/6.44  cnf(c_0_164, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_163, c_0_57]), c_0_153])).
% 6.25/6.44  cnf(c_0_165, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_69, c_0_164])).
% 6.25/6.44  cnf(c_0_166, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(spm,[status(thm)],[c_0_74, c_0_165])).
% 6.25/6.44  cnf(c_0_167, negated_conjecture, (v3_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0))), inference(spm,[status(thm)],[c_0_31, c_0_165])).
% 6.25/6.44  cnf(c_0_168, negated_conjecture, (r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_77, c_0_166])).
% 6.25/6.44  cnf(c_0_169, negated_conjecture, (r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_167]), c_0_168])])).
% 6.25/6.44  cnf(c_0_170, negated_conjecture, (r2_hidden(esk7_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0))), inference(spm,[status(thm)],[c_0_83, c_0_164])).
% 6.25/6.44  cnf(c_0_171, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_169]), c_0_170])]), ['proof']).
% 6.25/6.44  # SZS output end CNFRefutation
% 6.25/6.44  # Proof object total steps             : 172
% 6.25/6.44  # Proof object clause steps            : 139
% 6.25/6.44  # Proof object formula steps           : 33
% 6.25/6.44  # Proof object conjectures             : 106
% 6.25/6.44  # Proof object clause conjectures      : 103
% 6.25/6.44  # Proof object formula conjectures     : 3
% 6.25/6.44  # Proof object initial clauses used    : 27
% 6.25/6.44  # Proof object initial formulas used   : 16
% 6.25/6.44  # Proof object generating inferences   : 97
% 6.25/6.44  # Proof object simplifying inferences  : 41
% 6.25/6.44  # Training examples: 0 positive, 0 negative
% 6.25/6.44  # Parsed axioms                        : 18
% 6.25/6.44  # Removed by relevancy pruning/SinE    : 0
% 6.25/6.44  # Initial clauses                      : 38
% 6.25/6.44  # Removed in clause preprocessing      : 1
% 6.25/6.44  # Initial clauses in saturation        : 37
% 6.25/6.44  # Processed clauses                    : 11648
% 6.25/6.44  # ...of these trivial                  : 209
% 6.25/6.44  # ...subsumed                          : 5735
% 6.25/6.44  # ...remaining for further processing  : 5704
% 6.25/6.44  # Other redundant clauses eliminated   : 787
% 6.25/6.44  # Clauses deleted for lack of memory   : 0
% 6.25/6.44  # Backward-subsumed                    : 904
% 6.25/6.44  # Backward-rewritten                   : 767
% 6.25/6.44  # Generated clauses                    : 729349
% 6.25/6.44  # ...of the previous two non-trivial   : 621661
% 6.25/6.44  # Contextual simplify-reflections      : 69
% 6.25/6.44  # Paramodulations                      : 728526
% 6.25/6.44  # Factorizations                       : 4
% 6.25/6.44  # Equation resolutions                 : 787
% 6.25/6.44  # Propositional unsat checks           : 0
% 6.25/6.44  #    Propositional check models        : 0
% 6.25/6.44  #    Propositional check unsatisfiable : 0
% 6.25/6.44  #    Propositional clauses             : 0
% 6.25/6.44  #    Propositional clauses after purity: 0
% 6.25/6.44  #    Propositional unsat core size     : 0
% 6.25/6.44  #    Propositional preprocessing time  : 0.000
% 6.25/6.44  #    Propositional encoding time       : 0.000
% 6.25/6.44  #    Propositional solver time         : 0.000
% 6.25/6.44  #    Success case prop preproc time    : 0.000
% 6.25/6.44  #    Success case prop encoding time   : 0.000
% 6.25/6.44  #    Success case prop solver time     : 0.000
% 6.25/6.44  # Current number of processed clauses  : 3960
% 6.25/6.44  #    Positive orientable unit clauses  : 526
% 6.25/6.44  #    Positive unorientable unit clauses: 0
% 6.25/6.44  #    Negative unit clauses             : 69
% 6.25/6.44  #    Non-unit-clauses                  : 3365
% 6.25/6.44  # Current number of unprocessed clauses: 607801
% 6.25/6.44  # ...number of literals in the above   : 3099165
% 6.25/6.44  # Current number of archived formulas  : 0
% 6.25/6.44  # Current number of archived clauses   : 1739
% 6.25/6.44  # Clause-clause subsumption calls (NU) : 1518541
% 6.25/6.44  # Rec. Clause-clause subsumption calls : 667103
% 6.25/6.44  # Non-unit clause-clause subsumptions  : 5010
% 6.25/6.44  # Unit Clause-clause subsumption calls : 95346
% 6.25/6.44  # Rewrite failures with RHS unbound    : 0
% 6.25/6.44  # BW rewrite match attempts            : 1558
% 6.25/6.44  # BW rewrite match successes           : 111
% 6.25/6.44  # Condensation attempts                : 0
% 6.25/6.44  # Condensation successes               : 0
% 6.25/6.44  # Termbank termtop insertions          : 19910172
% 6.25/6.46  
% 6.25/6.46  # -------------------------------------------------
% 6.25/6.46  # User time                : 5.903 s
% 6.25/6.46  # System time              : 0.223 s
% 6.25/6.46  # Total time               : 6.127 s
% 6.25/6.46  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
