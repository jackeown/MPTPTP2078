%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:32 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :  151 (84256 expanded)
%              Number of clauses        :  116 (37756 expanded)
%              Number of leaves         :   17 (19764 expanded)
%              Depth                    :   41
%              Number of atoms          :  439 (345491 expanded)
%              Number of equality atoms :   38 (28015 expanded)
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

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(d2_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(t33_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
          <=> r1_ordinal1(k1_ordinal1(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

fof(t29_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k1_ordinal1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(t34_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,k1_ordinal1(X2))
          <=> r1_ordinal1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ( v4_ordinal1(X1)
        <=> ! [X2] :
              ( v3_ordinal1(X2)
             => ( r2_hidden(X2,X1)
               => r2_hidden(k1_ordinal1(X2),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t41_ordinal1])).

fof(c_0_18,plain,(
    ! [X38,X39] :
      ( ~ v3_ordinal1(X38)
      | ~ v3_ordinal1(X39)
      | r2_hidden(X38,X39)
      | X38 = X39
      | r2_hidden(X39,X38) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

fof(c_0_19,negated_conjecture,(
    ! [X53] :
      ( v3_ordinal1(esk8_0)
      & ( v3_ordinal1(esk9_0)
        | ~ v4_ordinal1(esk8_0) )
      & ( r2_hidden(esk9_0,esk8_0)
        | ~ v4_ordinal1(esk8_0) )
      & ( ~ r2_hidden(k1_ordinal1(esk9_0),esk8_0)
        | ~ v4_ordinal1(esk8_0) )
      & ( v4_ordinal1(esk8_0)
        | ~ v3_ordinal1(X53)
        | ~ r2_hidden(X53,esk8_0)
        | r2_hidden(k1_ordinal1(X53),esk8_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])])])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( v3_ordinal1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_22,plain,(
    ! [X45] :
      ( ( r2_hidden(esk6_1(X45),X45)
        | v3_ordinal1(k3_tarski(X45)) )
      & ( ~ v3_ordinal1(esk6_1(X45))
        | v3_ordinal1(k3_tarski(X45)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_ordinal1])])])])).

fof(c_0_23,plain,(
    ! [X32] :
      ( ( ~ v4_ordinal1(X32)
        | X32 = k3_tarski(X32) )
      & ( X32 != k3_tarski(X32)
        | v4_ordinal1(X32) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_ordinal1])])).

cnf(c_0_24,negated_conjecture,
    ( X1 = esk8_0
    | r2_hidden(X1,esk8_0)
    | r2_hidden(esk8_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( r2_hidden(esk6_1(X1),X1)
    | v3_ordinal1(k3_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X36,X37] :
      ( ~ v3_ordinal1(X37)
      | ~ r2_hidden(X36,X37)
      | v3_ordinal1(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

cnf(c_0_27,plain,
    ( v4_ordinal1(X1)
    | X1 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( k3_tarski(X1) = esk8_0
    | r2_hidden(esk8_0,k3_tarski(X1))
    | r2_hidden(k3_tarski(X1),esk8_0)
    | r2_hidden(esk6_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk9_0,esk8_0)
    | ~ v4_ordinal1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( v4_ordinal1(esk8_0)
    | r2_hidden(esk6_1(esk8_0),esk8_0)
    | r2_hidden(k3_tarski(esk8_0),esk8_0)
    | r2_hidden(esk8_0,k3_tarski(esk8_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28])])).

cnf(c_0_32,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk8_0,k3_tarski(esk8_0))
    | r2_hidden(k3_tarski(esk8_0),esk8_0)
    | r2_hidden(esk6_1(esk8_0),esk8_0)
    | r2_hidden(esk9_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,plain,
    ( v3_ordinal1(k3_tarski(X1))
    | ~ v3_ordinal1(esk6_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,negated_conjecture,
    ( v3_ordinal1(esk6_1(esk8_0))
    | r2_hidden(k3_tarski(esk8_0),esk8_0)
    | r2_hidden(esk8_0,k3_tarski(esk8_0))
    | r2_hidden(esk9_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_36,plain,(
    ! [X27] : k1_ordinal1(X27) = k2_xboole_0(X27,k1_tarski(X27)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_37,plain,(
    ! [X49,X50] :
      ( ~ r2_hidden(X49,X50)
      | ~ r1_tarski(X50,X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_38,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_39,negated_conjecture,
    ( v3_ordinal1(k3_tarski(esk8_0))
    | r2_hidden(esk8_0,k3_tarski(esk8_0))
    | r2_hidden(esk9_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( v4_ordinal1(esk8_0)
    | r2_hidden(k1_ordinal1(X1),esk8_0)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_41,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( k3_tarski(esk8_0) = esk8_0
    | r2_hidden(esk8_0,k3_tarski(esk8_0))
    | r2_hidden(k3_tarski(esk8_0),esk8_0)
    | r2_hidden(esk9_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_39])).

fof(c_0_45,plain,(
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

cnf(c_0_46,negated_conjecture,
    ( v4_ordinal1(esk8_0)
    | r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk8_0)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(k3_tarski(esk8_0),esk8_0)
    | r2_hidden(esk8_0,k3_tarski(esk8_0))
    | r2_hidden(esk9_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_44]),c_0_30])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( v4_ordinal1(esk8_0)
    | r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk8_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(csr,[status(thm)],[c_0_46,c_0_32])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk1_2(esk8_0,k3_tarski(esk8_0)),esk8_0)
    | r2_hidden(esk8_0,k3_tarski(esk8_0))
    | r2_hidden(esk9_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_52,plain,(
    ! [X35] : r2_hidden(X35,k1_ordinal1(X35)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk1_2(esk8_0,k3_tarski(esk8_0)),k1_tarski(esk1_2(esk8_0,k3_tarski(esk8_0)))),esk8_0)
    | r2_hidden(esk8_0,k3_tarski(esk8_0))
    | r2_hidden(esk9_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_30])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk8_0,k3_tarski(esk8_0))
    | r2_hidden(X1,k3_tarski(esk8_0))
    | r2_hidden(esk9_0,esk8_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk1_2(esk8_0,k3_tarski(esk8_0)),k1_tarski(esk1_2(esk8_0,k3_tarski(esk8_0))))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_55,c_0_41])).

fof(c_0_58,plain,(
    ! [X24] :
      ( ( v1_ordinal1(X24)
        | ~ v3_ordinal1(X24) )
      & ( v2_ordinal1(X24)
        | ~ v3_ordinal1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk1_2(esk8_0,k3_tarski(esk8_0)),k3_tarski(esk8_0))
    | r2_hidden(esk8_0,k3_tarski(esk8_0))
    | r2_hidden(esk9_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

fof(c_0_61,plain,(
    ! [X28,X29,X30] :
      ( ( ~ v1_ordinal1(X28)
        | ~ r2_hidden(X29,X28)
        | r1_tarski(X29,X28) )
      & ( r2_hidden(esk5_1(X30),X30)
        | v1_ordinal1(X30) )
      & ( ~ r1_tarski(esk5_1(X30),X30)
        | v1_ordinal1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

cnf(c_0_62,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_63,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk8_0,k3_tarski(esk8_0))
    | r2_hidden(esk9_0,esk8_0)
    | r1_tarski(esk8_0,k3_tarski(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_65,plain,
    ( r1_tarski(X2,X1)
    | ~ v1_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( v1_ordinal1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_21])).

cnf(c_0_67,plain,
    ( r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk8_0,k3_tarski(esk8_0))
    | r2_hidden(esk9_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_64]),c_0_48])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k3_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(X1,esk8_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk2_3(esk8_0,k3_tarski(esk8_0),esk8_0),esk8_0)
    | r2_hidden(esk9_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,esk2_3(X2,k3_tarski(X2),X1))
    | ~ r2_hidden(X1,k3_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk9_0,esk8_0)
    | r1_tarski(esk2_3(esk8_0,k3_tarski(esk8_0),esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk8_0,esk2_3(esk8_0,k3_tarski(esk8_0),esk8_0))
    | r2_hidden(esk9_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk9_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_73]),c_0_74])).

cnf(c_0_76,plain,
    ( X1 = k3_tarski(X1)
    | ~ v4_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_77,negated_conjecture,
    ( v4_ordinal1(esk8_0)
    | r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_75])).

fof(c_0_78,plain,(
    ! [X41,X42] :
      ( ( ~ r2_hidden(X41,X42)
        | r1_ordinal1(k1_ordinal1(X41),X42)
        | ~ v3_ordinal1(X42)
        | ~ v3_ordinal1(X41) )
      & ( ~ r1_ordinal1(k1_ordinal1(X41),X42)
        | r2_hidden(X41,X42)
        | ~ v3_ordinal1(X42)
        | ~ v3_ordinal1(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_ordinal1])])])])).

cnf(c_0_79,negated_conjecture,
    ( k3_tarski(esk8_0) = esk8_0
    | r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_80,plain,
    ( r1_ordinal1(k1_ordinal1(X1),X2)
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)
    | r2_hidden(esk2_3(esk8_0,esk8_0,X1),esk8_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_79])).

fof(c_0_82,plain,(
    ! [X40] :
      ( ~ v3_ordinal1(X40)
      | v3_ordinal1(k1_ordinal1(X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

cnf(c_0_83,plain,
    ( r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_80,c_0_41])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk2_3(esk8_0,esk8_0,esk9_0),esk8_0)
    | r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_75])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)
    | r2_hidden(X1,esk2_3(esk8_0,esk8_0,X1))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_79])).

fof(c_0_86,plain,(
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

cnf(c_0_87,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_88,plain,
    ( r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_83,c_0_29])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(esk2_3(esk8_0,esk8_0,esk9_0),esk8_0)
    | r2_hidden(X1,k3_tarski(esk8_0))
    | ~ r2_hidden(X1,k2_xboole_0(esk9_0,k1_tarski(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_84])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk9_0,esk2_3(esk8_0,esk8_0,esk9_0))
    | r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_75])).

cnf(c_0_91,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_92,plain,
    ( v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[c_0_87,c_0_41])).

cnf(c_0_93,negated_conjecture,
    ( v3_ordinal1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_75])).

cnf(c_0_94,negated_conjecture,
    ( r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),esk8_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_21])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk2_3(esk8_0,esk8_0,esk9_0),esk8_0)
    | r2_hidden(esk9_0,k3_tarski(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_57])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(esk9_0,esk2_3(esk8_0,esk8_0,esk9_0))
    | r2_hidden(X1,k3_tarski(esk8_0))
    | ~ r2_hidden(X1,k2_xboole_0(esk9_0,k1_tarski(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_90])).

fof(c_0_97,plain,(
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

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(X1,esk8_0)
    | ~ r1_ordinal1(X1,esk8_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_91,c_0_21])).

cnf(c_0_99,negated_conjecture,
    ( v3_ordinal1(k2_xboole_0(esk9_0,k1_tarski(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_100,negated_conjecture,
    ( r1_ordinal1(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_75])).

cnf(c_0_101,negated_conjecture,
    ( r2_hidden(esk9_0,k3_tarski(esk8_0))
    | r2_hidden(X1,k3_tarski(esk8_0))
    | ~ r2_hidden(X1,esk2_3(esk8_0,esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_95])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(esk9_0,esk2_3(esk8_0,esk8_0,esk9_0))
    | r2_hidden(esk9_0,k3_tarski(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_57])).

cnf(c_0_103,plain,
    ( r1_ordinal1(X1,X2)
    | ~ r2_hidden(X1,k1_ordinal1(X2))
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_100])])).

cnf(c_0_105,negated_conjecture,
    ( r2_hidden(esk9_0,k3_tarski(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_106,plain,
    ( r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_103,c_0_41])).

cnf(c_0_107,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(esk9_0,k1_tarski(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_99])).

cnf(c_0_108,negated_conjecture,
    ( k2_xboole_0(esk9_0,k1_tarski(esk9_0)) = esk8_0
    | r2_hidden(esk8_0,k2_xboole_0(esk9_0,k1_tarski(esk9_0)))
    | r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_99])).

cnf(c_0_109,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k2_xboole_0(esk9_0,k1_tarski(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_104])).

cnf(c_0_110,negated_conjecture,
    ( r2_hidden(esk2_3(esk8_0,k3_tarski(esk8_0),esk9_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_105])).

cnf(c_0_111,negated_conjecture,
    ( r1_ordinal1(X1,esk9_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk9_0,k1_tarski(esk9_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_93]),c_0_107])).

cnf(c_0_112,negated_conjecture,
    ( k2_xboole_0(esk9_0,k1_tarski(esk9_0)) = esk8_0
    | r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0) ),
    inference(sr,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_113,negated_conjecture,
    ( r1_tarski(X1,esk9_0)
    | ~ r1_ordinal1(X1,esk9_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_91,c_0_93])).

cnf(c_0_114,negated_conjecture,
    ( v3_ordinal1(esk2_3(esk8_0,k3_tarski(esk8_0),esk9_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_110])).

cnf(c_0_115,negated_conjecture,
    ( r1_ordinal1(X1,esk9_0)
    | r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_111,c_0_112])).

cnf(c_0_116,negated_conjecture,
    ( ~ r2_hidden(k1_ordinal1(esk9_0),esk8_0)
    | ~ v4_ordinal1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_117,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_118,negated_conjecture,
    ( r1_tarski(esk2_3(esk8_0,k3_tarski(esk8_0),esk9_0),esk9_0)
    | ~ r1_ordinal1(esk2_3(esk8_0,k3_tarski(esk8_0),esk9_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_113,c_0_114])).

cnf(c_0_119,negated_conjecture,
    ( r1_ordinal1(esk2_3(esk8_0,k3_tarski(esk8_0),esk9_0),esk9_0)
    | r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_115,c_0_110])).

cnf(c_0_120,negated_conjecture,
    ( ~ v4_ordinal1(esk8_0)
    | ~ r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0) ),
    inference(rw,[status(thm)],[c_0_116,c_0_41])).

cnf(c_0_121,plain,
    ( v4_ordinal1(X1)
    | r2_hidden(esk4_2(X1,X1),X1)
    | r2_hidden(esk3_2(X1,X1),X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_117])])).

cnf(c_0_122,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)
    | r1_tarski(esk2_3(esk8_0,k3_tarski(esk8_0),esk9_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_123,negated_conjecture,
    ( r2_hidden(esk9_0,esk2_3(esk8_0,k3_tarski(esk8_0),esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_105])).

cnf(c_0_124,negated_conjecture,
    ( r2_hidden(esk3_2(esk8_0,esk8_0),esk8_0)
    | r2_hidden(esk4_2(esk8_0,esk8_0),esk8_0)
    | ~ r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_120,c_0_121])).

cnf(c_0_125,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_122]),c_0_123])])).

cnf(c_0_126,plain,
    ( r2_hidden(esk3_2(X1,X2),esk4_2(X1,X2))
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_127,negated_conjecture,
    ( r2_hidden(esk4_2(esk8_0,esk8_0),esk8_0)
    | r2_hidden(esk3_2(esk8_0,esk8_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_124,c_0_125])])).

cnf(c_0_128,plain,
    ( v4_ordinal1(X1)
    | r2_hidden(esk3_2(X1,X1),esk4_2(X1,X1))
    | r2_hidden(esk3_2(X1,X1),X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_126])])).

cnf(c_0_129,negated_conjecture,
    ( r2_hidden(esk8_0,k3_tarski(esk8_0))
    | r2_hidden(k3_tarski(esk8_0),esk8_0)
    | r2_hidden(esk6_1(esk8_0),esk8_0)
    | ~ r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_120,c_0_31])).

cnf(c_0_130,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_131,negated_conjecture,
    ( r2_hidden(esk3_2(esk8_0,esk8_0),esk8_0)
    | r1_tarski(esk4_2(esk8_0,esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_127])).

cnf(c_0_132,negated_conjecture,
    ( r2_hidden(esk3_2(esk8_0,esk8_0),esk4_2(esk8_0,esk8_0))
    | r2_hidden(esk3_2(esk8_0,esk8_0),esk8_0)
    | ~ r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_120,c_0_128])).

cnf(c_0_133,negated_conjecture,
    ( r2_hidden(esk6_1(esk8_0),esk8_0)
    | r2_hidden(k3_tarski(esk8_0),esk8_0)
    | r2_hidden(esk8_0,k3_tarski(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_129,c_0_125])])).

cnf(c_0_134,negated_conjecture,
    ( r2_hidden(esk3_2(esk8_0,esk8_0),esk8_0)
    | r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X1,esk4_2(esk8_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_130,c_0_131])).

cnf(c_0_135,negated_conjecture,
    ( r2_hidden(esk3_2(esk8_0,esk8_0),esk4_2(esk8_0,esk8_0))
    | r2_hidden(esk3_2(esk8_0,esk8_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_132,c_0_125])])).

cnf(c_0_136,negated_conjecture,
    ( v3_ordinal1(esk6_1(esk8_0))
    | r2_hidden(esk8_0,k3_tarski(esk8_0))
    | r2_hidden(k3_tarski(esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_133])).

cnf(c_0_137,negated_conjecture,
    ( r2_hidden(esk3_2(esk8_0,esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_134,c_0_135])).

cnf(c_0_138,negated_conjecture,
    ( ~ v4_ordinal1(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_120,c_0_125])])).

fof(c_0_139,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_140,negated_conjecture,
    ( v3_ordinal1(k3_tarski(esk8_0))
    | r2_hidden(esk8_0,k3_tarski(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_136]),c_0_32])).

cnf(c_0_141,plain,
    ( X2 = k3_tarski(X1)
    | ~ r2_hidden(esk3_2(X1,X2),X2)
    | ~ r2_hidden(esk3_2(X1,X2),X3)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_142,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk3_2(esk8_0,esk8_0),k1_tarski(esk3_2(esk8_0,esk8_0))),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_137]),c_0_138])).

cnf(c_0_143,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_139])).

cnf(c_0_144,negated_conjecture,
    ( k3_tarski(esk8_0) = esk8_0
    | r2_hidden(esk8_0,k3_tarski(esk8_0))
    | r2_hidden(k3_tarski(esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_140])).

cnf(c_0_145,negated_conjecture,
    ( X1 = k3_tarski(esk8_0)
    | ~ r2_hidden(esk3_2(esk8_0,X1),k2_xboole_0(esk3_2(esk8_0,esk8_0),k1_tarski(esk3_2(esk8_0,esk8_0))))
    | ~ r2_hidden(esk3_2(esk8_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_141,c_0_142])).

cnf(c_0_146,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_143])).

cnf(c_0_147,negated_conjecture,
    ( r2_hidden(k3_tarski(esk8_0),esk8_0)
    | r2_hidden(esk8_0,k3_tarski(esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_144]),c_0_138])).

cnf(c_0_148,negated_conjecture,
    ( k3_tarski(esk8_0) = esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_137]),c_0_57])])).

cnf(c_0_149,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_146])).

cnf(c_0_150,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_147,c_0_148]),c_0_148])]),c_0_149]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:25:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 2.27/2.47  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 2.27/2.47  # and selection function SelectCQIArEqFirst.
% 2.27/2.47  #
% 2.27/2.47  # Preprocessing time       : 0.030 s
% 2.27/2.47  # Presaturation interreduction done
% 2.27/2.47  
% 2.27/2.47  # Proof found!
% 2.27/2.47  # SZS status Theorem
% 2.27/2.47  # SZS output start CNFRefutation
% 2.27/2.47  fof(t41_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_ordinal1)).
% 2.27/2.47  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 2.27/2.47  fof(t35_ordinal1, axiom, ![X1]:(![X2]:(r2_hidden(X2,X1)=>v3_ordinal1(X2))=>v3_ordinal1(k3_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_ordinal1)).
% 2.27/2.47  fof(d6_ordinal1, axiom, ![X1]:(v4_ordinal1(X1)<=>X1=k3_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_ordinal1)).
% 2.27/2.47  fof(t23_ordinal1, axiom, ![X1, X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>v3_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_ordinal1)).
% 2.27/2.47  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 2.27/2.47  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.27/2.47  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.27/2.47  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 2.27/2.47  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 2.27/2.47  fof(cc1_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(v1_ordinal1(X1)&v2_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 2.27/2.47  fof(d2_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)<=>![X2]:(r2_hidden(X2,X1)=>r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 2.27/2.47  fof(t33_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)<=>r1_ordinal1(k1_ordinal1(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 2.27/2.47  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 2.27/2.47  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 2.27/2.47  fof(t34_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 2.27/2.47  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.27/2.47  fof(c_0_17, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1)))))), inference(assume_negation,[status(cth)],[t41_ordinal1])).
% 2.27/2.47  fof(c_0_18, plain, ![X38, X39]:(~v3_ordinal1(X38)|(~v3_ordinal1(X39)|(r2_hidden(X38,X39)|X38=X39|r2_hidden(X39,X38)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 2.27/2.47  fof(c_0_19, negated_conjecture, ![X53]:(v3_ordinal1(esk8_0)&(((v3_ordinal1(esk9_0)|~v4_ordinal1(esk8_0))&((r2_hidden(esk9_0,esk8_0)|~v4_ordinal1(esk8_0))&(~r2_hidden(k1_ordinal1(esk9_0),esk8_0)|~v4_ordinal1(esk8_0))))&(v4_ordinal1(esk8_0)|(~v3_ordinal1(X53)|(~r2_hidden(X53,esk8_0)|r2_hidden(k1_ordinal1(X53),esk8_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])])])).
% 2.27/2.47  cnf(c_0_20, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.27/2.47  cnf(c_0_21, negated_conjecture, (v3_ordinal1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.27/2.47  fof(c_0_22, plain, ![X45]:((r2_hidden(esk6_1(X45),X45)|v3_ordinal1(k3_tarski(X45)))&(~v3_ordinal1(esk6_1(X45))|v3_ordinal1(k3_tarski(X45)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_ordinal1])])])])).
% 2.27/2.47  fof(c_0_23, plain, ![X32]:((~v4_ordinal1(X32)|X32=k3_tarski(X32))&(X32!=k3_tarski(X32)|v4_ordinal1(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_ordinal1])])).
% 2.27/2.47  cnf(c_0_24, negated_conjecture, (X1=esk8_0|r2_hidden(X1,esk8_0)|r2_hidden(esk8_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 2.27/2.47  cnf(c_0_25, plain, (r2_hidden(esk6_1(X1),X1)|v3_ordinal1(k3_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.27/2.47  fof(c_0_26, plain, ![X36, X37]:(~v3_ordinal1(X37)|(~r2_hidden(X36,X37)|v3_ordinal1(X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).
% 2.27/2.47  cnf(c_0_27, plain, (v4_ordinal1(X1)|X1!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.27/2.47  cnf(c_0_28, negated_conjecture, (k3_tarski(X1)=esk8_0|r2_hidden(esk8_0,k3_tarski(X1))|r2_hidden(k3_tarski(X1),esk8_0)|r2_hidden(esk6_1(X1),X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 2.27/2.47  cnf(c_0_29, plain, (v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.27/2.47  cnf(c_0_30, negated_conjecture, (r2_hidden(esk9_0,esk8_0)|~v4_ordinal1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.27/2.47  cnf(c_0_31, negated_conjecture, (v4_ordinal1(esk8_0)|r2_hidden(esk6_1(esk8_0),esk8_0)|r2_hidden(k3_tarski(esk8_0),esk8_0)|r2_hidden(esk8_0,k3_tarski(esk8_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28])])).
% 2.27/2.47  cnf(c_0_32, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_29, c_0_21])).
% 2.27/2.47  cnf(c_0_33, negated_conjecture, (r2_hidden(esk8_0,k3_tarski(esk8_0))|r2_hidden(k3_tarski(esk8_0),esk8_0)|r2_hidden(esk6_1(esk8_0),esk8_0)|r2_hidden(esk9_0,esk8_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 2.27/2.47  cnf(c_0_34, plain, (v3_ordinal1(k3_tarski(X1))|~v3_ordinal1(esk6_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.27/2.47  cnf(c_0_35, negated_conjecture, (v3_ordinal1(esk6_1(esk8_0))|r2_hidden(k3_tarski(esk8_0),esk8_0)|r2_hidden(esk8_0,k3_tarski(esk8_0))|r2_hidden(esk9_0,esk8_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 2.27/2.47  fof(c_0_36, plain, ![X27]:k1_ordinal1(X27)=k2_xboole_0(X27,k1_tarski(X27)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 2.27/2.47  fof(c_0_37, plain, ![X49, X50]:(~r2_hidden(X49,X50)|~r1_tarski(X50,X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 2.27/2.47  fof(c_0_38, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 2.27/2.47  cnf(c_0_39, negated_conjecture, (v3_ordinal1(k3_tarski(esk8_0))|r2_hidden(esk8_0,k3_tarski(esk8_0))|r2_hidden(esk9_0,esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_32])).
% 2.27/2.47  cnf(c_0_40, negated_conjecture, (v4_ordinal1(esk8_0)|r2_hidden(k1_ordinal1(X1),esk8_0)|~v3_ordinal1(X1)|~r2_hidden(X1,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.27/2.47  cnf(c_0_41, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 2.27/2.47  cnf(c_0_42, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 2.27/2.47  cnf(c_0_43, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 2.27/2.47  cnf(c_0_44, negated_conjecture, (k3_tarski(esk8_0)=esk8_0|r2_hidden(esk8_0,k3_tarski(esk8_0))|r2_hidden(k3_tarski(esk8_0),esk8_0)|r2_hidden(esk9_0,esk8_0)), inference(spm,[status(thm)],[c_0_24, c_0_39])).
% 2.27/2.47  fof(c_0_45, plain, ![X13, X14, X15, X17, X18, X19, X20, X22]:((((r2_hidden(X15,esk2_3(X13,X14,X15))|~r2_hidden(X15,X14)|X14!=k3_tarski(X13))&(r2_hidden(esk2_3(X13,X14,X15),X13)|~r2_hidden(X15,X14)|X14!=k3_tarski(X13)))&(~r2_hidden(X17,X18)|~r2_hidden(X18,X13)|r2_hidden(X17,X14)|X14!=k3_tarski(X13)))&((~r2_hidden(esk3_2(X19,X20),X20)|(~r2_hidden(esk3_2(X19,X20),X22)|~r2_hidden(X22,X19))|X20=k3_tarski(X19))&((r2_hidden(esk3_2(X19,X20),esk4_2(X19,X20))|r2_hidden(esk3_2(X19,X20),X20)|X20=k3_tarski(X19))&(r2_hidden(esk4_2(X19,X20),X19)|r2_hidden(esk3_2(X19,X20),X20)|X20=k3_tarski(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 2.27/2.47  cnf(c_0_46, negated_conjecture, (v4_ordinal1(esk8_0)|r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk8_0)|~v3_ordinal1(X1)|~r2_hidden(X1,esk8_0)), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 2.27/2.47  cnf(c_0_47, plain, (r2_hidden(esk1_2(X1,X2),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 2.27/2.47  cnf(c_0_48, negated_conjecture, (r2_hidden(k3_tarski(esk8_0),esk8_0)|r2_hidden(esk8_0,k3_tarski(esk8_0))|r2_hidden(esk9_0,esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_44]), c_0_30])).
% 2.27/2.47  cnf(c_0_49, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 2.27/2.47  cnf(c_0_50, negated_conjecture, (v4_ordinal1(esk8_0)|r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk8_0)|~r2_hidden(X1,esk8_0)), inference(csr,[status(thm)],[c_0_46, c_0_32])).
% 2.27/2.47  cnf(c_0_51, negated_conjecture, (r2_hidden(esk1_2(esk8_0,k3_tarski(esk8_0)),esk8_0)|r2_hidden(esk8_0,k3_tarski(esk8_0))|r2_hidden(esk9_0,esk8_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 2.27/2.47  fof(c_0_52, plain, ![X35]:r2_hidden(X35,k1_ordinal1(X35)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 2.27/2.47  cnf(c_0_53, plain, (r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X3,X2)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_49])).
% 2.27/2.47  cnf(c_0_54, negated_conjecture, (r2_hidden(k2_xboole_0(esk1_2(esk8_0,k3_tarski(esk8_0)),k1_tarski(esk1_2(esk8_0,k3_tarski(esk8_0)))),esk8_0)|r2_hidden(esk8_0,k3_tarski(esk8_0))|r2_hidden(esk9_0,esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_30])).
% 2.27/2.47  cnf(c_0_55, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 2.27/2.47  cnf(c_0_56, negated_conjecture, (r2_hidden(esk8_0,k3_tarski(esk8_0))|r2_hidden(X1,k3_tarski(esk8_0))|r2_hidden(esk9_0,esk8_0)|~r2_hidden(X1,k2_xboole_0(esk1_2(esk8_0,k3_tarski(esk8_0)),k1_tarski(esk1_2(esk8_0,k3_tarski(esk8_0)))))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 2.27/2.47  cnf(c_0_57, plain, (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_55, c_0_41])).
% 2.27/2.47  fof(c_0_58, plain, ![X24]:((v1_ordinal1(X24)|~v3_ordinal1(X24))&(v2_ordinal1(X24)|~v3_ordinal1(X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).
% 2.27/2.47  cnf(c_0_59, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 2.27/2.47  cnf(c_0_60, negated_conjecture, (r2_hidden(esk1_2(esk8_0,k3_tarski(esk8_0)),k3_tarski(esk8_0))|r2_hidden(esk8_0,k3_tarski(esk8_0))|r2_hidden(esk9_0,esk8_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 2.27/2.47  fof(c_0_61, plain, ![X28, X29, X30]:((~v1_ordinal1(X28)|(~r2_hidden(X29,X28)|r1_tarski(X29,X28)))&((r2_hidden(esk5_1(X30),X30)|v1_ordinal1(X30))&(~r1_tarski(esk5_1(X30),X30)|v1_ordinal1(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).
% 2.27/2.47  cnf(c_0_62, plain, (v1_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 2.27/2.47  cnf(c_0_63, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|X2!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 2.27/2.47  cnf(c_0_64, negated_conjecture, (r2_hidden(esk8_0,k3_tarski(esk8_0))|r2_hidden(esk9_0,esk8_0)|r1_tarski(esk8_0,k3_tarski(esk8_0))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 2.27/2.47  cnf(c_0_65, plain, (r1_tarski(X2,X1)|~v1_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 2.27/2.47  cnf(c_0_66, negated_conjecture, (v1_ordinal1(esk8_0)), inference(spm,[status(thm)],[c_0_62, c_0_21])).
% 2.27/2.47  cnf(c_0_67, plain, (r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)|~r2_hidden(X2,k3_tarski(X1))), inference(er,[status(thm)],[c_0_63])).
% 2.27/2.47  cnf(c_0_68, negated_conjecture, (r2_hidden(esk8_0,k3_tarski(esk8_0))|r2_hidden(esk9_0,esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_64]), c_0_48])).
% 2.27/2.47  cnf(c_0_69, plain, (r2_hidden(X1,esk2_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k3_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 2.27/2.47  cnf(c_0_70, negated_conjecture, (r1_tarski(X1,esk8_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 2.27/2.47  cnf(c_0_71, negated_conjecture, (r2_hidden(esk2_3(esk8_0,k3_tarski(esk8_0),esk8_0),esk8_0)|r2_hidden(esk9_0,esk8_0)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 2.27/2.47  cnf(c_0_72, plain, (r2_hidden(X1,esk2_3(X2,k3_tarski(X2),X1))|~r2_hidden(X1,k3_tarski(X2))), inference(er,[status(thm)],[c_0_69])).
% 2.27/2.47  cnf(c_0_73, negated_conjecture, (r2_hidden(esk9_0,esk8_0)|r1_tarski(esk2_3(esk8_0,k3_tarski(esk8_0),esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 2.27/2.47  cnf(c_0_74, negated_conjecture, (r2_hidden(esk8_0,esk2_3(esk8_0,k3_tarski(esk8_0),esk8_0))|r2_hidden(esk9_0,esk8_0)), inference(spm,[status(thm)],[c_0_72, c_0_68])).
% 2.27/2.47  cnf(c_0_75, negated_conjecture, (r2_hidden(esk9_0,esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_73]), c_0_74])).
% 2.27/2.47  cnf(c_0_76, plain, (X1=k3_tarski(X1)|~v4_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.27/2.47  cnf(c_0_77, negated_conjecture, (v4_ordinal1(esk8_0)|r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)), inference(spm,[status(thm)],[c_0_50, c_0_75])).
% 2.27/2.47  fof(c_0_78, plain, ![X41, X42]:((~r2_hidden(X41,X42)|r1_ordinal1(k1_ordinal1(X41),X42)|~v3_ordinal1(X42)|~v3_ordinal1(X41))&(~r1_ordinal1(k1_ordinal1(X41),X42)|r2_hidden(X41,X42)|~v3_ordinal1(X42)|~v3_ordinal1(X41))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_ordinal1])])])])).
% 2.27/2.47  cnf(c_0_79, negated_conjecture, (k3_tarski(esk8_0)=esk8_0|r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 2.27/2.47  cnf(c_0_80, plain, (r1_ordinal1(k1_ordinal1(X1),X2)|~r2_hidden(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 2.27/2.47  cnf(c_0_81, negated_conjecture, (r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)|r2_hidden(esk2_3(esk8_0,esk8_0,X1),esk8_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_67, c_0_79])).
% 2.27/2.47  fof(c_0_82, plain, ![X40]:(~v3_ordinal1(X40)|v3_ordinal1(k1_ordinal1(X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 2.27/2.47  cnf(c_0_83, plain, (r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_80, c_0_41])).
% 2.27/2.47  cnf(c_0_84, negated_conjecture, (r2_hidden(esk2_3(esk8_0,esk8_0,esk9_0),esk8_0)|r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)), inference(spm,[status(thm)],[c_0_81, c_0_75])).
% 2.27/2.47  cnf(c_0_85, negated_conjecture, (r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)|r2_hidden(X1,esk2_3(esk8_0,esk8_0,X1))|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_72, c_0_79])).
% 2.27/2.47  fof(c_0_86, plain, ![X33, X34]:((~r1_ordinal1(X33,X34)|r1_tarski(X33,X34)|(~v3_ordinal1(X33)|~v3_ordinal1(X34)))&(~r1_tarski(X33,X34)|r1_ordinal1(X33,X34)|(~v3_ordinal1(X33)|~v3_ordinal1(X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 2.27/2.47  cnf(c_0_87, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 2.27/2.47  cnf(c_0_88, plain, (r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_83, c_0_29])).
% 2.27/2.47  cnf(c_0_89, negated_conjecture, (r2_hidden(esk2_3(esk8_0,esk8_0,esk9_0),esk8_0)|r2_hidden(X1,k3_tarski(esk8_0))|~r2_hidden(X1,k2_xboole_0(esk9_0,k1_tarski(esk9_0)))), inference(spm,[status(thm)],[c_0_53, c_0_84])).
% 2.27/2.47  cnf(c_0_90, negated_conjecture, (r2_hidden(esk9_0,esk2_3(esk8_0,esk8_0,esk9_0))|r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)), inference(spm,[status(thm)],[c_0_85, c_0_75])).
% 2.27/2.47  cnf(c_0_91, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 2.27/2.47  cnf(c_0_92, plain, (v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_87, c_0_41])).
% 2.27/2.47  cnf(c_0_93, negated_conjecture, (v3_ordinal1(esk9_0)), inference(spm,[status(thm)],[c_0_32, c_0_75])).
% 2.27/2.47  cnf(c_0_94, negated_conjecture, (r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),esk8_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_88, c_0_21])).
% 2.27/2.47  cnf(c_0_95, negated_conjecture, (r2_hidden(esk2_3(esk8_0,esk8_0,esk9_0),esk8_0)|r2_hidden(esk9_0,k3_tarski(esk8_0))), inference(spm,[status(thm)],[c_0_89, c_0_57])).
% 2.27/2.47  cnf(c_0_96, negated_conjecture, (r2_hidden(esk9_0,esk2_3(esk8_0,esk8_0,esk9_0))|r2_hidden(X1,k3_tarski(esk8_0))|~r2_hidden(X1,k2_xboole_0(esk9_0,k1_tarski(esk9_0)))), inference(spm,[status(thm)],[c_0_53, c_0_90])).
% 2.27/2.47  fof(c_0_97, plain, ![X43, X44]:((~r2_hidden(X43,k1_ordinal1(X44))|r1_ordinal1(X43,X44)|~v3_ordinal1(X44)|~v3_ordinal1(X43))&(~r1_ordinal1(X43,X44)|r2_hidden(X43,k1_ordinal1(X44))|~v3_ordinal1(X44)|~v3_ordinal1(X43))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).
% 2.27/2.47  cnf(c_0_98, negated_conjecture, (r1_tarski(X1,esk8_0)|~r1_ordinal1(X1,esk8_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_91, c_0_21])).
% 2.27/2.47  cnf(c_0_99, negated_conjecture, (v3_ordinal1(k2_xboole_0(esk9_0,k1_tarski(esk9_0)))), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 2.27/2.47  cnf(c_0_100, negated_conjecture, (r1_ordinal1(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)), inference(spm,[status(thm)],[c_0_94, c_0_75])).
% 2.27/2.47  cnf(c_0_101, negated_conjecture, (r2_hidden(esk9_0,k3_tarski(esk8_0))|r2_hidden(X1,k3_tarski(esk8_0))|~r2_hidden(X1,esk2_3(esk8_0,esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_53, c_0_95])).
% 2.27/2.47  cnf(c_0_102, negated_conjecture, (r2_hidden(esk9_0,esk2_3(esk8_0,esk8_0,esk9_0))|r2_hidden(esk9_0,k3_tarski(esk8_0))), inference(spm,[status(thm)],[c_0_96, c_0_57])).
% 2.27/2.47  cnf(c_0_103, plain, (r1_ordinal1(X1,X2)|~r2_hidden(X1,k1_ordinal1(X2))|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_97])).
% 2.27/2.47  cnf(c_0_104, negated_conjecture, (r1_tarski(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_100])])).
% 2.27/2.47  cnf(c_0_105, negated_conjecture, (r2_hidden(esk9_0,k3_tarski(esk8_0))), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 2.27/2.47  cnf(c_0_106, plain, (r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_103, c_0_41])).
% 2.27/2.47  cnf(c_0_107, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(esk9_0,k1_tarski(esk9_0)))), inference(spm,[status(thm)],[c_0_29, c_0_99])).
% 2.27/2.47  cnf(c_0_108, negated_conjecture, (k2_xboole_0(esk9_0,k1_tarski(esk9_0))=esk8_0|r2_hidden(esk8_0,k2_xboole_0(esk9_0,k1_tarski(esk9_0)))|r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)), inference(spm,[status(thm)],[c_0_24, c_0_99])).
% 2.27/2.47  cnf(c_0_109, negated_conjecture, (~r2_hidden(esk8_0,k2_xboole_0(esk9_0,k1_tarski(esk9_0)))), inference(spm,[status(thm)],[c_0_42, c_0_104])).
% 2.27/2.47  cnf(c_0_110, negated_conjecture, (r2_hidden(esk2_3(esk8_0,k3_tarski(esk8_0),esk9_0),esk8_0)), inference(spm,[status(thm)],[c_0_67, c_0_105])).
% 2.27/2.47  cnf(c_0_111, negated_conjecture, (r1_ordinal1(X1,esk9_0)|~r2_hidden(X1,k2_xboole_0(esk9_0,k1_tarski(esk9_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_93]), c_0_107])).
% 2.27/2.47  cnf(c_0_112, negated_conjecture, (k2_xboole_0(esk9_0,k1_tarski(esk9_0))=esk8_0|r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)), inference(sr,[status(thm)],[c_0_108, c_0_109])).
% 2.27/2.47  cnf(c_0_113, negated_conjecture, (r1_tarski(X1,esk9_0)|~r1_ordinal1(X1,esk9_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_91, c_0_93])).
% 2.27/2.47  cnf(c_0_114, negated_conjecture, (v3_ordinal1(esk2_3(esk8_0,k3_tarski(esk8_0),esk9_0))), inference(spm,[status(thm)],[c_0_32, c_0_110])).
% 2.27/2.47  cnf(c_0_115, negated_conjecture, (r1_ordinal1(X1,esk9_0)|r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_111, c_0_112])).
% 2.27/2.47  cnf(c_0_116, negated_conjecture, (~r2_hidden(k1_ordinal1(esk9_0),esk8_0)|~v4_ordinal1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.27/2.47  cnf(c_0_117, plain, (r2_hidden(esk4_2(X1,X2),X1)|r2_hidden(esk3_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 2.27/2.47  cnf(c_0_118, negated_conjecture, (r1_tarski(esk2_3(esk8_0,k3_tarski(esk8_0),esk9_0),esk9_0)|~r1_ordinal1(esk2_3(esk8_0,k3_tarski(esk8_0),esk9_0),esk9_0)), inference(spm,[status(thm)],[c_0_113, c_0_114])).
% 2.27/2.47  cnf(c_0_119, negated_conjecture, (r1_ordinal1(esk2_3(esk8_0,k3_tarski(esk8_0),esk9_0),esk9_0)|r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)), inference(spm,[status(thm)],[c_0_115, c_0_110])).
% 2.27/2.47  cnf(c_0_120, negated_conjecture, (~v4_ordinal1(esk8_0)|~r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)), inference(rw,[status(thm)],[c_0_116, c_0_41])).
% 2.27/2.47  cnf(c_0_121, plain, (v4_ordinal1(X1)|r2_hidden(esk4_2(X1,X1),X1)|r2_hidden(esk3_2(X1,X1),X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_117])])).
% 2.27/2.47  cnf(c_0_122, negated_conjecture, (r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)|r1_tarski(esk2_3(esk8_0,k3_tarski(esk8_0),esk9_0),esk9_0)), inference(spm,[status(thm)],[c_0_118, c_0_119])).
% 2.27/2.47  cnf(c_0_123, negated_conjecture, (r2_hidden(esk9_0,esk2_3(esk8_0,k3_tarski(esk8_0),esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_105])).
% 2.27/2.47  cnf(c_0_124, negated_conjecture, (r2_hidden(esk3_2(esk8_0,esk8_0),esk8_0)|r2_hidden(esk4_2(esk8_0,esk8_0),esk8_0)|~r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)), inference(spm,[status(thm)],[c_0_120, c_0_121])).
% 2.27/2.47  cnf(c_0_125, negated_conjecture, (r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_122]), c_0_123])])).
% 2.27/2.47  cnf(c_0_126, plain, (r2_hidden(esk3_2(X1,X2),esk4_2(X1,X2))|r2_hidden(esk3_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 2.27/2.47  cnf(c_0_127, negated_conjecture, (r2_hidden(esk4_2(esk8_0,esk8_0),esk8_0)|r2_hidden(esk3_2(esk8_0,esk8_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_124, c_0_125])])).
% 2.27/2.47  cnf(c_0_128, plain, (v4_ordinal1(X1)|r2_hidden(esk3_2(X1,X1),esk4_2(X1,X1))|r2_hidden(esk3_2(X1,X1),X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_126])])).
% 2.27/2.47  cnf(c_0_129, negated_conjecture, (r2_hidden(esk8_0,k3_tarski(esk8_0))|r2_hidden(k3_tarski(esk8_0),esk8_0)|r2_hidden(esk6_1(esk8_0),esk8_0)|~r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)), inference(spm,[status(thm)],[c_0_120, c_0_31])).
% 2.27/2.47  cnf(c_0_130, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 2.27/2.47  cnf(c_0_131, negated_conjecture, (r2_hidden(esk3_2(esk8_0,esk8_0),esk8_0)|r1_tarski(esk4_2(esk8_0,esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_70, c_0_127])).
% 2.27/2.47  cnf(c_0_132, negated_conjecture, (r2_hidden(esk3_2(esk8_0,esk8_0),esk4_2(esk8_0,esk8_0))|r2_hidden(esk3_2(esk8_0,esk8_0),esk8_0)|~r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)), inference(spm,[status(thm)],[c_0_120, c_0_128])).
% 2.27/2.47  cnf(c_0_133, negated_conjecture, (r2_hidden(esk6_1(esk8_0),esk8_0)|r2_hidden(k3_tarski(esk8_0),esk8_0)|r2_hidden(esk8_0,k3_tarski(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_129, c_0_125])])).
% 2.27/2.47  cnf(c_0_134, negated_conjecture, (r2_hidden(esk3_2(esk8_0,esk8_0),esk8_0)|r2_hidden(X1,esk8_0)|~r2_hidden(X1,esk4_2(esk8_0,esk8_0))), inference(spm,[status(thm)],[c_0_130, c_0_131])).
% 2.27/2.47  cnf(c_0_135, negated_conjecture, (r2_hidden(esk3_2(esk8_0,esk8_0),esk4_2(esk8_0,esk8_0))|r2_hidden(esk3_2(esk8_0,esk8_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_132, c_0_125])])).
% 2.27/2.47  cnf(c_0_136, negated_conjecture, (v3_ordinal1(esk6_1(esk8_0))|r2_hidden(esk8_0,k3_tarski(esk8_0))|r2_hidden(k3_tarski(esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_32, c_0_133])).
% 2.27/2.47  cnf(c_0_137, negated_conjecture, (r2_hidden(esk3_2(esk8_0,esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_134, c_0_135])).
% 2.27/2.47  cnf(c_0_138, negated_conjecture, (~v4_ordinal1(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_120, c_0_125])])).
% 2.27/2.47  fof(c_0_139, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 2.27/2.47  cnf(c_0_140, negated_conjecture, (v3_ordinal1(k3_tarski(esk8_0))|r2_hidden(esk8_0,k3_tarski(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_136]), c_0_32])).
% 2.27/2.47  cnf(c_0_141, plain, (X2=k3_tarski(X1)|~r2_hidden(esk3_2(X1,X2),X2)|~r2_hidden(esk3_2(X1,X2),X3)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 2.27/2.47  cnf(c_0_142, negated_conjecture, (r2_hidden(k2_xboole_0(esk3_2(esk8_0,esk8_0),k1_tarski(esk3_2(esk8_0,esk8_0))),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_137]), c_0_138])).
% 2.27/2.47  cnf(c_0_143, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_139])).
% 2.27/2.47  cnf(c_0_144, negated_conjecture, (k3_tarski(esk8_0)=esk8_0|r2_hidden(esk8_0,k3_tarski(esk8_0))|r2_hidden(k3_tarski(esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_24, c_0_140])).
% 2.27/2.47  cnf(c_0_145, negated_conjecture, (X1=k3_tarski(esk8_0)|~r2_hidden(esk3_2(esk8_0,X1),k2_xboole_0(esk3_2(esk8_0,esk8_0),k1_tarski(esk3_2(esk8_0,esk8_0))))|~r2_hidden(esk3_2(esk8_0,X1),X1)), inference(spm,[status(thm)],[c_0_141, c_0_142])).
% 2.27/2.47  cnf(c_0_146, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_143])).
% 2.27/2.47  cnf(c_0_147, negated_conjecture, (r2_hidden(k3_tarski(esk8_0),esk8_0)|r2_hidden(esk8_0,k3_tarski(esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_144]), c_0_138])).
% 2.27/2.47  cnf(c_0_148, negated_conjecture, (k3_tarski(esk8_0)=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_137]), c_0_57])])).
% 2.27/2.47  cnf(c_0_149, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_42, c_0_146])).
% 2.27/2.47  cnf(c_0_150, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_147, c_0_148]), c_0_148])]), c_0_149]), ['proof']).
% 2.27/2.47  # SZS output end CNFRefutation
% 2.27/2.47  # Proof object total steps             : 151
% 2.27/2.47  # Proof object clause steps            : 116
% 2.27/2.47  # Proof object formula steps           : 35
% 2.27/2.47  # Proof object conjectures             : 81
% 2.27/2.47  # Proof object clause conjectures      : 78
% 2.27/2.47  # Proof object formula conjectures     : 3
% 2.27/2.47  # Proof object initial clauses used    : 29
% 2.27/2.47  # Proof object initial formulas used   : 17
% 2.27/2.47  # Proof object generating inferences   : 69
% 2.27/2.47  # Proof object simplifying inferences  : 43
% 2.27/2.47  # Training examples: 0 positive, 0 negative
% 2.27/2.47  # Parsed axioms                        : 19
% 2.27/2.47  # Removed by relevancy pruning/SinE    : 0
% 2.27/2.47  # Initial clauses                      : 41
% 2.27/2.47  # Removed in clause preprocessing      : 1
% 2.27/2.47  # Initial clauses in saturation        : 40
% 2.27/2.47  # Processed clauses                    : 4883
% 2.27/2.47  # ...of these trivial                  : 174
% 2.27/2.47  # ...subsumed                          : 1680
% 2.27/2.47  # ...remaining for further processing  : 3029
% 2.27/2.47  # Other redundant clauses eliminated   : 24
% 2.27/2.47  # Clauses deleted for lack of memory   : 0
% 2.27/2.47  # Backward-subsumed                    : 275
% 2.27/2.47  # Backward-rewritten                   : 728
% 2.27/2.47  # Generated clauses                    : 227741
% 2.27/2.47  # ...of the previous two non-trivial   : 217969
% 2.27/2.47  # Contextual simplify-reflections      : 38
% 2.27/2.47  # Paramodulations                      : 227708
% 2.27/2.47  # Factorizations                       : 0
% 2.27/2.47  # Equation resolutions                 : 24
% 2.27/2.47  # Propositional unsat checks           : 0
% 2.27/2.47  #    Propositional check models        : 0
% 2.27/2.47  #    Propositional check unsatisfiable : 0
% 2.27/2.47  #    Propositional clauses             : 0
% 2.27/2.47  #    Propositional clauses after purity: 0
% 2.27/2.47  #    Propositional unsat core size     : 0
% 2.27/2.47  #    Propositional preprocessing time  : 0.000
% 2.27/2.47  #    Propositional encoding time       : 0.000
% 2.27/2.47  #    Propositional solver time         : 0.000
% 2.27/2.47  #    Success case prop preproc time    : 0.000
% 2.27/2.47  #    Success case prop encoding time   : 0.000
% 2.27/2.47  #    Success case prop solver time     : 0.000
% 2.27/2.47  # Current number of processed clauses  : 1973
% 2.27/2.47  #    Positive orientable unit clauses  : 480
% 2.27/2.47  #    Positive unorientable unit clauses: 0
% 2.27/2.47  #    Negative unit clauses             : 127
% 2.27/2.47  #    Non-unit-clauses                  : 1366
% 2.27/2.47  # Current number of unprocessed clauses: 212457
% 2.27/2.47  # ...number of literals in the above   : 1041409
% 2.27/2.47  # Current number of archived formulas  : 0
% 2.27/2.47  # Current number of archived clauses   : 1052
% 2.27/2.47  # Clause-clause subsumption calls (NU) : 200449
% 2.27/2.47  # Rec. Clause-clause subsumption calls : 112830
% 2.27/2.47  # Non-unit clause-clause subsumptions  : 1344
% 2.27/2.47  # Unit Clause-clause subsumption calls : 20430
% 2.27/2.47  # Rewrite failures with RHS unbound    : 0
% 2.27/2.47  # BW rewrite match attempts            : 627
% 2.27/2.47  # BW rewrite match successes           : 69
% 2.27/2.47  # Condensation attempts                : 0
% 2.27/2.47  # Condensation successes               : 0
% 2.27/2.47  # Termbank termtop insertions          : 5512345
% 2.27/2.48  
% 2.27/2.48  # -------------------------------------------------
% 2.27/2.48  # User time                : 2.053 s
% 2.27/2.48  # System time              : 0.083 s
% 2.27/2.48  # Total time               : 2.136 s
% 2.27/2.48  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
