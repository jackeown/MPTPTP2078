%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:27 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 213 expanded)
%              Number of clauses        :   43 (  91 expanded)
%              Number of leaves         :   12 (  51 expanded)
%              Depth                    :   13
%              Number of atoms          :  226 ( 820 expanded)
%              Number of equality atoms :   39 ( 115 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,k1_ordinal1(X2))
          <=> r1_ordinal1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(t21_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_xboole_0(X1,X2)
           => r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(d2_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t26_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r1_ordinal1(X1,X2)
            | r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X1,k1_ordinal1(X2))
            <=> r1_ordinal1(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_ordinal1])).

fof(c_0_13,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X14,X13)
        | r2_hidden(X14,X11)
        | r2_hidden(X14,X12)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X13)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k2_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k2_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X18)
        | r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k2_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_14,negated_conjecture,
    ( v3_ordinal1(esk5_0)
    & v3_ordinal1(esk6_0)
    & ( ~ r2_hidden(esk5_0,k1_ordinal1(esk6_0))
      | ~ r1_ordinal1(esk5_0,esk6_0) )
    & ( r2_hidden(esk5_0,k1_ordinal1(esk6_0))
      | r1_ordinal1(esk5_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_15,plain,(
    ! [X30] : k1_ordinal1(X30) = k2_xboole_0(X30,k1_tarski(X30)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_16,plain,(
    ! [X22,X23,X24,X25,X26,X27] :
      ( ( ~ r2_hidden(X24,X23)
        | X24 = X22
        | X23 != k1_tarski(X22) )
      & ( X25 != X22
        | r2_hidden(X25,X23)
        | X23 != k1_tarski(X22) )
      & ( ~ r2_hidden(esk3_2(X26,X27),X27)
        | esk3_2(X26,X27) != X26
        | X27 = k1_tarski(X26) )
      & ( r2_hidden(esk3_2(X26,X27),X27)
        | esk3_2(X26,X27) = X26
        | X27 = k1_tarski(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk5_0,k1_ordinal1(esk6_0))
    | r1_ordinal1(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k1_ordinal1(esk6_0))
    | ~ r1_ordinal1(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( r1_ordinal1(esk5_0,esk6_0)
    | r2_hidden(esk5_0,k2_xboole_0(esk6_0,k1_tarski(esk6_0))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( ~ r1_ordinal1(esk5_0,esk6_0)
    | ~ r2_hidden(esk5_0,k2_xboole_0(esk6_0,k1_tarski(esk6_0))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_21])).

fof(c_0_27,plain,(
    ! [X35,X36] :
      ( ( ~ r1_ordinal1(X35,X36)
        | r1_tarski(X35,X36)
        | ~ v3_ordinal1(X35)
        | ~ v3_ordinal1(X36) )
      & ( ~ r1_tarski(X35,X36)
        | r1_ordinal1(X35,X36)
        | ~ v3_ordinal1(X35)
        | ~ v3_ordinal1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

fof(c_0_28,plain,(
    ! [X37,X38] :
      ( ~ v1_ordinal1(X37)
      | ~ v3_ordinal1(X38)
      | ~ r2_xboole_0(X37,X38)
      | r2_hidden(X37,X38) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_ordinal1])])])).

fof(c_0_29,plain,(
    ! [X20,X21] :
      ( ( r1_tarski(X20,X21)
        | ~ r2_xboole_0(X20,X21) )
      & ( X20 != X21
        | ~ r2_xboole_0(X20,X21) )
      & ( ~ r1_tarski(X20,X21)
        | X20 = X21
        | r2_xboole_0(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_30,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( r1_ordinal1(esk5_0,esk6_0)
    | r2_hidden(esk5_0,k1_tarski(esk6_0))
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( ~ r1_ordinal1(esk5_0,esk6_0)
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( r1_ordinal1(X1,X2)
    | ~ r1_tarski(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( v3_ordinal1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( v3_ordinal1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_36,plain,(
    ! [X31,X32,X33] :
      ( ( ~ v1_ordinal1(X31)
        | ~ r2_hidden(X32,X31)
        | r1_tarski(X32,X31) )
      & ( r2_hidden(esk4_1(X33),X33)
        | v1_ordinal1(X33) )
      & ( ~ r1_tarski(esk4_1(X33),X33)
        | v1_ordinal1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( esk5_0 = esk6_0
    | r1_ordinal1(esk5_0,esk6_0)
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( ~ r2_hidden(esk5_0,esk6_0)
    | ~ r1_tarski(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])])).

cnf(c_0_42,plain,
    ( r1_tarski(X2,X1)
    | ~ v1_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( esk5_0 = esk6_0
    | r2_hidden(esk5_0,esk6_0)
    | r1_tarski(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_34]),c_0_35])])).

cnf(c_0_45,negated_conjecture,
    ( ~ v1_ordinal1(esk6_0)
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( esk5_0 = esk6_0
    | r2_hidden(esk5_0,esk6_0)
    | ~ v1_ordinal1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_34])])).

fof(c_0_47,plain,(
    ! [X29] :
      ( ( v1_ordinal1(X29)
        | ~ v3_ordinal1(X29) )
      & ( v2_ordinal1(X29)
        | ~ v3_ordinal1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_49,negated_conjecture,
    ( esk5_0 = esk6_0
    | ~ v1_ordinal1(esk6_0)
    | ~ v1_ordinal1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_51,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( esk5_0 = esk6_0
    | ~ v1_ordinal1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_35])])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_55,plain,(
    ! [X41,X42] :
      ( ~ r2_hidden(X41,X42)
      | ~ r1_tarski(X42,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_ordinal1(esk5_0,esk6_0)
    | ~ r2_hidden(esk5_0,k1_tarski(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( esk5_0 = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_50]),c_0_34])])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_54])])).

fof(c_0_61,plain,(
    ! [X39,X40] :
      ( ~ v3_ordinal1(X39)
      | ~ v3_ordinal1(X40)
      | r1_ordinal1(X39,X40)
      | r2_hidden(X40,X39) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_ordinal1(esk6_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59]),c_0_59]),c_0_60])])).

cnf(c_0_65,plain,
    ( r1_ordinal1(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_66,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_34])]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:32:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.12/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.031 s
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t34_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 0.12/0.37  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.12/0.37  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.12/0.37  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.12/0.37  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.12/0.37  fof(t21_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_xboole_0(X1,X2)=>r2_hidden(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_ordinal1)).
% 0.12/0.37  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.12/0.37  fof(d2_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)<=>![X2]:(r2_hidden(X2,X1)=>r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 0.12/0.37  fof(cc1_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(v1_ordinal1(X1)&v2_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 0.12/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.37  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.12/0.37  fof(t26_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r1_ordinal1(X1,X2)|r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 0.12/0.37  fof(c_0_12, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2))))), inference(assume_negation,[status(cth)],[t34_ordinal1])).
% 0.12/0.37  fof(c_0_13, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X14,X13)|(r2_hidden(X14,X11)|r2_hidden(X14,X12))|X13!=k2_xboole_0(X11,X12))&((~r2_hidden(X15,X11)|r2_hidden(X15,X13)|X13!=k2_xboole_0(X11,X12))&(~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k2_xboole_0(X11,X12))))&(((~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k2_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|~r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k2_xboole_0(X16,X17)))&(r2_hidden(esk2_3(X16,X17,X18),X18)|(r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k2_xboole_0(X16,X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.12/0.37  fof(c_0_14, negated_conjecture, (v3_ordinal1(esk5_0)&(v3_ordinal1(esk6_0)&((~r2_hidden(esk5_0,k1_ordinal1(esk6_0))|~r1_ordinal1(esk5_0,esk6_0))&(r2_hidden(esk5_0,k1_ordinal1(esk6_0))|r1_ordinal1(esk5_0,esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.12/0.37  fof(c_0_15, plain, ![X30]:k1_ordinal1(X30)=k2_xboole_0(X30,k1_tarski(X30)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.12/0.37  fof(c_0_16, plain, ![X22, X23, X24, X25, X26, X27]:(((~r2_hidden(X24,X23)|X24=X22|X23!=k1_tarski(X22))&(X25!=X22|r2_hidden(X25,X23)|X23!=k1_tarski(X22)))&((~r2_hidden(esk3_2(X26,X27),X27)|esk3_2(X26,X27)!=X26|X27=k1_tarski(X26))&(r2_hidden(esk3_2(X26,X27),X27)|esk3_2(X26,X27)=X26|X27=k1_tarski(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.12/0.37  cnf(c_0_17, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_18, negated_conjecture, (r2_hidden(esk5_0,k1_ordinal1(esk6_0))|r1_ordinal1(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.37  cnf(c_0_19, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_20, negated_conjecture, (~r2_hidden(esk5_0,k1_ordinal1(esk6_0))|~r1_ordinal1(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.37  cnf(c_0_21, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_22, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_23, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k2_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_24, negated_conjecture, (r1_ordinal1(esk5_0,esk6_0)|r2_hidden(esk5_0,k2_xboole_0(esk6_0,k1_tarski(esk6_0)))), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.37  cnf(c_0_25, negated_conjecture, (~r1_ordinal1(esk5_0,esk6_0)|~r2_hidden(esk5_0,k2_xboole_0(esk6_0,k1_tarski(esk6_0)))), inference(rw,[status(thm)],[c_0_20, c_0_19])).
% 0.12/0.37  cnf(c_0_26, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_21])).
% 0.12/0.37  fof(c_0_27, plain, ![X35, X36]:((~r1_ordinal1(X35,X36)|r1_tarski(X35,X36)|(~v3_ordinal1(X35)|~v3_ordinal1(X36)))&(~r1_tarski(X35,X36)|r1_ordinal1(X35,X36)|(~v3_ordinal1(X35)|~v3_ordinal1(X36)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.12/0.37  fof(c_0_28, plain, ![X37, X38]:(~v1_ordinal1(X37)|(~v3_ordinal1(X38)|(~r2_xboole_0(X37,X38)|r2_hidden(X37,X38)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_ordinal1])])])).
% 0.12/0.37  fof(c_0_29, plain, ![X20, X21]:(((r1_tarski(X20,X21)|~r2_xboole_0(X20,X21))&(X20!=X21|~r2_xboole_0(X20,X21)))&(~r1_tarski(X20,X21)|X20=X21|r2_xboole_0(X20,X21))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.12/0.37  cnf(c_0_30, plain, (X1=X2|~r2_hidden(X1,k1_tarski(X2))), inference(er,[status(thm)],[c_0_22])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (r1_ordinal1(esk5_0,esk6_0)|r2_hidden(esk5_0,k1_tarski(esk6_0))|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.12/0.37  cnf(c_0_32, negated_conjecture, (~r1_ordinal1(esk5_0,esk6_0)|~r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.37  cnf(c_0_33, plain, (r1_ordinal1(X1,X2)|~r1_tarski(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (v3_ordinal1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.37  cnf(c_0_35, negated_conjecture, (v3_ordinal1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.37  fof(c_0_36, plain, ![X31, X32, X33]:((~v1_ordinal1(X31)|(~r2_hidden(X32,X31)|r1_tarski(X32,X31)))&((r2_hidden(esk4_1(X33),X33)|v1_ordinal1(X33))&(~r1_tarski(esk4_1(X33),X33)|v1_ordinal1(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).
% 0.12/0.37  cnf(c_0_37, plain, (r2_hidden(X1,X2)|~v1_ordinal1(X1)|~v3_ordinal1(X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.37  cnf(c_0_38, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.37  cnf(c_0_39, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.37  cnf(c_0_40, negated_conjecture, (esk5_0=esk6_0|r1_ordinal1(esk5_0,esk6_0)|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.12/0.37  cnf(c_0_41, negated_conjecture, (~r2_hidden(esk5_0,esk6_0)|~r1_tarski(esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35])])).
% 0.12/0.37  cnf(c_0_42, plain, (r1_tarski(X2,X1)|~v1_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.37  cnf(c_0_43, plain, (X1=X2|r2_hidden(X1,X2)|~v1_ordinal1(X1)|~v3_ordinal1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.12/0.37  cnf(c_0_44, negated_conjecture, (esk5_0=esk6_0|r2_hidden(esk5_0,esk6_0)|r1_tarski(esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_34]), c_0_35])])).
% 0.12/0.37  cnf(c_0_45, negated_conjecture, (~v1_ordinal1(esk6_0)|~r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.12/0.37  cnf(c_0_46, negated_conjecture, (esk5_0=esk6_0|r2_hidden(esk5_0,esk6_0)|~v1_ordinal1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_34])])).
% 0.12/0.37  fof(c_0_47, plain, ![X29]:((v1_ordinal1(X29)|~v3_ordinal1(X29))&(v2_ordinal1(X29)|~v3_ordinal1(X29))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).
% 0.12/0.37  cnf(c_0_48, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_49, negated_conjecture, (esk5_0=esk6_0|~v1_ordinal1(esk6_0)|~v1_ordinal1(esk5_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.12/0.37  cnf(c_0_50, plain, (v1_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.12/0.37  fof(c_0_51, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.37  cnf(c_0_52, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_48])).
% 0.12/0.37  cnf(c_0_53, negated_conjecture, (esk5_0=esk6_0|~v1_ordinal1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_35])])).
% 0.12/0.37  cnf(c_0_54, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  fof(c_0_55, plain, ![X41, X42]:(~r2_hidden(X41,X42)|~r1_tarski(X42,X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.12/0.37  cnf(c_0_56, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.12/0.37  cnf(c_0_57, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.12/0.37  cnf(c_0_58, negated_conjecture, (~r1_ordinal1(esk5_0,esk6_0)|~r2_hidden(esk5_0,k1_tarski(esk6_0))), inference(spm,[status(thm)],[c_0_25, c_0_52])).
% 0.12/0.37  cnf(c_0_59, negated_conjecture, (esk5_0=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_50]), c_0_34])])).
% 0.12/0.37  cnf(c_0_60, plain, (r2_hidden(X1,k1_tarski(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_54])])).
% 0.12/0.37  fof(c_0_61, plain, ![X39, X40]:(~v3_ordinal1(X39)|(~v3_ordinal1(X40)|(r1_ordinal1(X39,X40)|r2_hidden(X40,X39)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).
% 0.12/0.37  cnf(c_0_62, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.12/0.37  cnf(c_0_63, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.12/0.37  cnf(c_0_64, negated_conjecture, (~r1_ordinal1(esk6_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59]), c_0_59]), c_0_60])])).
% 0.12/0.37  cnf(c_0_65, plain, (r1_ordinal1(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.12/0.37  cnf(c_0_66, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.12/0.37  cnf(c_0_67, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_34])]), c_0_66]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 68
% 0.12/0.37  # Proof object clause steps            : 43
% 0.12/0.37  # Proof object formula steps           : 25
% 0.12/0.37  # Proof object conjectures             : 22
% 0.12/0.37  # Proof object clause conjectures      : 19
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 20
% 0.12/0.37  # Proof object initial formulas used   : 12
% 0.12/0.37  # Proof object generating inferences   : 15
% 0.12/0.37  # Proof object simplifying inferences  : 27
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 12
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 31
% 0.12/0.37  # Removed in clause preprocessing      : 1
% 0.12/0.37  # Initial clauses in saturation        : 30
% 0.12/0.37  # Processed clauses                    : 78
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 2
% 0.12/0.37  # ...remaining for further processing  : 76
% 0.12/0.37  # Other redundant clauses eliminated   : 7
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 2
% 0.12/0.37  # Backward-rewritten                   : 21
% 0.12/0.37  # Generated clauses                    : 125
% 0.12/0.37  # ...of the previous two non-trivial   : 114
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 113
% 0.12/0.37  # Factorizations                       : 6
% 0.12/0.37  # Equation resolutions                 : 7
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 47
% 0.12/0.37  #    Positive orientable unit clauses  : 4
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 10
% 0.12/0.37  #    Non-unit-clauses                  : 33
% 0.12/0.37  # Current number of unprocessed clauses: 66
% 0.12/0.37  # ...number of literals in the above   : 206
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 24
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 556
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 264
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 3
% 0.12/0.37  # Unit Clause-clause subsumption calls : 60
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 6
% 0.12/0.37  # BW rewrite match successes           : 1
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 3270
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.036 s
% 0.12/0.37  # System time              : 0.004 s
% 0.12/0.37  # Total time               : 0.040 s
% 0.12/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
