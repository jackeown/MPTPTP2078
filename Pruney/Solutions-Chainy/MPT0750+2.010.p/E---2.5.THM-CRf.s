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
% DateTime   : Thu Dec  3 10:56:33 EST 2020

% Result     : Theorem 16.92s
% Output     : CNFRefutation 16.92s
% Verified   : 
% Statistics : Number of formulae       :  141 (62183 expanded)
%              Number of clauses        :  110 (28224 expanded)
%              Number of leaves         :   15 (14507 expanded)
%              Depth                    :   45
%              Number of atoms          :  399 (248978 expanded)
%              Number of equality atoms :   37 (24771 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t29_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k1_ordinal1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

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

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(t33_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
          <=> r1_ordinal1(k1_ordinal1(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ( v4_ordinal1(X1)
        <=> ! [X2] :
              ( v3_ordinal1(X2)
             => ( r2_hidden(X2,X1)
               => r2_hidden(k1_ordinal1(X2),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t41_ordinal1])).

fof(c_0_16,plain,(
    ! [X35,X36] :
      ( ~ v3_ordinal1(X35)
      | ~ v3_ordinal1(X36)
      | r2_hidden(X35,X36)
      | X35 = X36
      | r2_hidden(X36,X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

fof(c_0_17,negated_conjecture,(
    ! [X51] :
      ( v3_ordinal1(esk7_0)
      & ( v3_ordinal1(esk8_0)
        | ~ v4_ordinal1(esk7_0) )
      & ( r2_hidden(esk8_0,esk7_0)
        | ~ v4_ordinal1(esk7_0) )
      & ( ~ r2_hidden(k1_ordinal1(esk8_0),esk7_0)
        | ~ v4_ordinal1(esk7_0) )
      & ( v4_ordinal1(esk7_0)
        | ~ v3_ordinal1(X51)
        | ~ r2_hidden(X51,esk7_0)
        | r2_hidden(k1_ordinal1(X51),esk7_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( v3_ordinal1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_20,plain,(
    ! [X42] :
      ( ( r2_hidden(esk5_1(X42),X42)
        | v3_ordinal1(k3_tarski(X42)) )
      & ( ~ v3_ordinal1(esk5_1(X42))
        | v3_ordinal1(k3_tarski(X42)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_ordinal1])])])])).

fof(c_0_21,plain,(
    ! [X27] :
      ( ( ~ v4_ordinal1(X27)
        | X27 = k3_tarski(X27) )
      & ( X27 != k3_tarski(X27)
        | v4_ordinal1(X27) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_ordinal1])])).

cnf(c_0_22,negated_conjecture,
    ( X1 = esk7_0
    | r2_hidden(X1,esk7_0)
    | r2_hidden(esk7_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( r2_hidden(esk5_1(X1),X1)
    | v3_ordinal1(k3_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X33,X34] :
      ( ~ v3_ordinal1(X34)
      | ~ r2_hidden(X33,X34)
      | v3_ordinal1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

cnf(c_0_25,plain,
    ( v4_ordinal1(X1)
    | X1 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( k3_tarski(X1) = esk7_0
    | r2_hidden(esk7_0,k3_tarski(X1))
    | r2_hidden(k3_tarski(X1),esk7_0)
    | r2_hidden(esk5_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0)
    | ~ v4_ordinal1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( v4_ordinal1(esk7_0)
    | r2_hidden(esk5_1(esk7_0),esk7_0)
    | r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26])])).

cnf(c_0_30,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk5_1(esk7_0),esk7_0)
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_32,plain,(
    ! [X26] : k1_ordinal1(X26) = k2_xboole_0(X26,k1_tarski(X26)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

cnf(c_0_33,plain,
    ( v3_ordinal1(k3_tarski(X1))
    | ~ v3_ordinal1(esk5_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,negated_conjecture,
    ( v3_ordinal1(esk5_1(esk7_0))
    | r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( v4_ordinal1(esk7_0)
    | r2_hidden(k1_ordinal1(X1),esk7_0)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_36,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( v3_ordinal1(k3_tarski(esk7_0))
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_30])).

fof(c_0_38,plain,(
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

cnf(c_0_39,negated_conjecture,
    ( v4_ordinal1(esk7_0)
    | r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk7_0)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( k3_tarski(esk7_0) = esk7_0
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_37])).

fof(c_0_41,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_42,plain,(
    ! [X37] :
      ( ~ v3_ordinal1(X37)
      | v3_ordinal1(k1_ordinal1(X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( v4_ordinal1(esk7_0)
    | r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(csr,[status(thm)],[c_0_39,c_0_30])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_40]),c_0_28])).

fof(c_0_46,plain,(
    ! [X30] : r2_hidden(X30,k1_ordinal1(X30)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

fof(c_0_47,plain,(
    ! [X47,X48] :
      ( ~ r2_hidden(X47,X48)
      | ~ r1_tarski(X48,X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k2_xboole_0(k3_tarski(esk7_0),k1_tarski(k3_tarski(esk7_0))),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_28])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_48])).

fof(c_0_55,plain,(
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

cnf(c_0_56,plain,
    ( v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[c_0_49,c_0_36])).

fof(c_0_57,plain,(
    ! [X31,X32] :
      ( ( ~ r2_hidden(X31,k1_ordinal1(X32))
        | r2_hidden(X31,X32)
        | X31 = X32 )
      & ( ~ r2_hidden(X31,X32)
        | r2_hidden(X31,k1_ordinal1(X32)) )
      & ( X31 != X32
        | r2_hidden(X31,k1_ordinal1(X32)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).

cnf(c_0_58,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(X1,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0)
    | ~ r2_hidden(X1,k2_xboole_0(k3_tarski(esk7_0),k1_tarski(k3_tarski(esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_52,c_0_36])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,plain,
    ( r1_ordinal1(X1,X2)
    | ~ r2_hidden(X1,k1_ordinal1(X2))
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( v3_ordinal1(k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_19])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,plain,
    ( r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

fof(c_0_67,plain,(
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

cnf(c_0_68,plain,
    ( r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_62,c_0_36])).

cnf(c_0_69,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_63])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_64,c_0_36])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( r1_ordinal1(X1,esk7_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_19]),c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k3_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(X1,esk7_0)
    | ~ r1_ordinal1(X1,esk7_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_19])).

cnf(c_0_77,negated_conjecture,
    ( v3_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,esk2_3(X2,k3_tarski(X2),X1))
    | ~ r2_hidden(X1,k3_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0)
    | r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk7_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_66])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_80]),c_0_81])).

cnf(c_0_83,plain,
    ( X1 = k3_tarski(X1)
    | ~ v4_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_84,negated_conjecture,
    ( v4_ordinal1(esk7_0)
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_82])).

cnf(c_0_85,negated_conjecture,
    ( k3_tarski(esk7_0) = esk7_0
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

fof(c_0_86,plain,(
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

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | r2_hidden(esk2_3(esk7_0,esk7_0,X1),esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_85])).

cnf(c_0_88,plain,
    ( r1_ordinal1(k1_ordinal1(X1),X2)
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,esk7_0,esk8_0),esk7_0)
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_82])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | r2_hidden(X1,esk2_3(esk7_0,esk7_0,X1))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_85])).

cnf(c_0_91,plain,
    ( r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_88,c_0_36])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,esk7_0,esk8_0),esk7_0)
    | r2_hidden(X1,k3_tarski(esk7_0))
    | ~ r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_89])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk8_0,esk2_3(esk7_0,esk7_0,esk8_0))
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_82])).

cnf(c_0_94,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_95,plain,
    ( r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_91,c_0_27])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,esk7_0,esk8_0),esk7_0)
    | r2_hidden(esk8_0,k3_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_60])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(esk8_0,esk2_3(esk7_0,esk7_0,esk8_0))
    | r2_hidden(X1,k3_tarski(esk7_0))
    | ~ r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( v3_ordinal1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_82])).

cnf(c_0_99,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r1_ordinal1(X1,X2) ),
    inference(rw,[status(thm)],[c_0_94,c_0_36])).

cnf(c_0_100,negated_conjecture,
    ( r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_19])).

cnf(c_0_101,negated_conjecture,
    ( r2_hidden(esk8_0,k3_tarski(esk7_0))
    | r2_hidden(X1,k3_tarski(esk7_0))
    | ~ r2_hidden(X1,esk2_3(esk7_0,esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_96])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(esk8_0,esk2_3(esk7_0,esk7_0,esk8_0))
    | r2_hidden(esk8_0,k3_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_60])).

cnf(c_0_103,negated_conjecture,
    ( v3_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_98])).

cnf(c_0_104,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | ~ r2_hidden(X1,k1_ordinal1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_105,negated_conjecture,
    ( r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))
    | ~ r1_ordinal1(X1,esk7_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_99,c_0_19])).

cnf(c_0_106,negated_conjecture,
    ( r1_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_100,c_0_82])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(esk8_0,k3_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_108,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_103])).

cnf(c_0_109,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_104,c_0_36])).

cnf(c_0_110,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_103]),c_0_106])])).

cnf(c_0_111,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_107])).

cnf(c_0_112,negated_conjecture,
    ( r1_ordinal1(X1,esk8_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_98]),c_0_108])).

cnf(c_0_113,negated_conjecture,
    ( k2_xboole_0(esk8_0,k1_tarski(esk8_0)) = esk7_0
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(X1,esk8_0)
    | ~ r1_ordinal1(X1,esk8_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_98])).

cnf(c_0_115,negated_conjecture,
    ( v3_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_111])).

cnf(c_0_116,negated_conjecture,
    ( r1_ordinal1(X1,esk8_0)
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_117,negated_conjecture,
    ( ~ r2_hidden(k1_ordinal1(esk8_0),esk7_0)
    | ~ v4_ordinal1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_118,negated_conjecture,
    ( r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)
    | ~ r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_119,negated_conjecture,
    ( r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_116,c_0_111])).

cnf(c_0_120,negated_conjecture,
    ( ~ v4_ordinal1(esk7_0)
    | ~ r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(rw,[status(thm)],[c_0_117,c_0_36])).

cnf(c_0_121,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_122,negated_conjecture,
    ( r2_hidden(esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_107])).

cnf(c_0_123,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk5_1(esk7_0),esk7_0)
    | ~ r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_120,c_0_29])).

cnf(c_0_124,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_121]),c_0_122])])).

cnf(c_0_125,negated_conjecture,
    ( r2_hidden(esk5_1(esk7_0),esk7_0)
    | r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_123,c_0_124])])).

cnf(c_0_126,negated_conjecture,
    ( v3_ordinal1(esk5_1(esk7_0))
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(k3_tarski(esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_125])).

cnf(c_0_127,negated_conjecture,
    ( v3_ordinal1(k3_tarski(esk7_0))
    | r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_126]),c_0_30])).

cnf(c_0_128,negated_conjecture,
    ( k3_tarski(esk7_0) = esk7_0
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(k3_tarski(esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_127])).

cnf(c_0_129,negated_conjecture,
    ( ~ v4_ordinal1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_120,c_0_124])])).

cnf(c_0_130,negated_conjecture,
    ( r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_128]),c_0_129])).

cnf(c_0_131,negated_conjecture,
    ( r2_hidden(k2_xboole_0(k3_tarski(esk7_0),k1_tarski(k3_tarski(esk7_0))),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_130]),c_0_129])).

cnf(c_0_132,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(X1,k3_tarski(esk7_0))
    | ~ r2_hidden(X1,k2_xboole_0(k3_tarski(esk7_0),k1_tarski(k3_tarski(esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_131])).

cnf(c_0_133,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_60]),c_0_61])).

cnf(c_0_134,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_133])).

cnf(c_0_135,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_134])).

cnf(c_0_136,negated_conjecture,
    ( v3_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_134])).

cnf(c_0_137,negated_conjecture,
    ( r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_135])).

cnf(c_0_138,negated_conjecture,
    ( r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_136]),c_0_137])])).

cnf(c_0_139,negated_conjecture,
    ( r2_hidden(esk7_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_133])).

cnf(c_0_140,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_138]),c_0_139])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:00:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 16.92/17.14  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 16.92/17.14  # and selection function SelectCQIArEqFirst.
% 16.92/17.14  #
% 16.92/17.14  # Preprocessing time       : 0.029 s
% 16.92/17.14  # Presaturation interreduction done
% 16.92/17.14  
% 16.92/17.14  # Proof found!
% 16.92/17.14  # SZS status Theorem
% 16.92/17.14  # SZS output start CNFRefutation
% 16.92/17.14  fof(t41_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_ordinal1)).
% 16.92/17.14  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 16.92/17.14  fof(t35_ordinal1, axiom, ![X1]:(![X2]:(r2_hidden(X2,X1)=>v3_ordinal1(X2))=>v3_ordinal1(k3_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_ordinal1)).
% 16.92/17.14  fof(d6_ordinal1, axiom, ![X1]:(v4_ordinal1(X1)<=>X1=k3_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_ordinal1)).
% 16.92/17.14  fof(t23_ordinal1, axiom, ![X1, X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>v3_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_ordinal1)).
% 16.92/17.14  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 16.92/17.14  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 16.92/17.14  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 16.92/17.14  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 16.92/17.14  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 16.92/17.14  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 16.92/17.14  fof(t34_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 16.92/17.14  fof(t13_ordinal1, axiom, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 16.92/17.14  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 16.92/17.14  fof(t33_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)<=>r1_ordinal1(k1_ordinal1(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 16.92/17.14  fof(c_0_15, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1)))))), inference(assume_negation,[status(cth)],[t41_ordinal1])).
% 16.92/17.14  fof(c_0_16, plain, ![X35, X36]:(~v3_ordinal1(X35)|(~v3_ordinal1(X36)|(r2_hidden(X35,X36)|X35=X36|r2_hidden(X36,X35)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 16.92/17.14  fof(c_0_17, negated_conjecture, ![X51]:(v3_ordinal1(esk7_0)&(((v3_ordinal1(esk8_0)|~v4_ordinal1(esk7_0))&((r2_hidden(esk8_0,esk7_0)|~v4_ordinal1(esk7_0))&(~r2_hidden(k1_ordinal1(esk8_0),esk7_0)|~v4_ordinal1(esk7_0))))&(v4_ordinal1(esk7_0)|(~v3_ordinal1(X51)|(~r2_hidden(X51,esk7_0)|r2_hidden(k1_ordinal1(X51),esk7_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])])).
% 16.92/17.14  cnf(c_0_18, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 16.92/17.14  cnf(c_0_19, negated_conjecture, (v3_ordinal1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 16.92/17.14  fof(c_0_20, plain, ![X42]:((r2_hidden(esk5_1(X42),X42)|v3_ordinal1(k3_tarski(X42)))&(~v3_ordinal1(esk5_1(X42))|v3_ordinal1(k3_tarski(X42)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_ordinal1])])])])).
% 16.92/17.14  fof(c_0_21, plain, ![X27]:((~v4_ordinal1(X27)|X27=k3_tarski(X27))&(X27!=k3_tarski(X27)|v4_ordinal1(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_ordinal1])])).
% 16.92/17.14  cnf(c_0_22, negated_conjecture, (X1=esk7_0|r2_hidden(X1,esk7_0)|r2_hidden(esk7_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 16.92/17.14  cnf(c_0_23, plain, (r2_hidden(esk5_1(X1),X1)|v3_ordinal1(k3_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 16.92/17.14  fof(c_0_24, plain, ![X33, X34]:(~v3_ordinal1(X34)|(~r2_hidden(X33,X34)|v3_ordinal1(X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).
% 16.92/17.14  cnf(c_0_25, plain, (v4_ordinal1(X1)|X1!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 16.92/17.14  cnf(c_0_26, negated_conjecture, (k3_tarski(X1)=esk7_0|r2_hidden(esk7_0,k3_tarski(X1))|r2_hidden(k3_tarski(X1),esk7_0)|r2_hidden(esk5_1(X1),X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 16.92/17.14  cnf(c_0_27, plain, (v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 16.92/17.14  cnf(c_0_28, negated_conjecture, (r2_hidden(esk8_0,esk7_0)|~v4_ordinal1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 16.92/17.14  cnf(c_0_29, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(esk5_1(esk7_0),esk7_0)|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26])])).
% 16.92/17.14  cnf(c_0_30, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_27, c_0_19])).
% 16.92/17.14  cnf(c_0_31, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk5_1(esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 16.92/17.14  fof(c_0_32, plain, ![X26]:k1_ordinal1(X26)=k2_xboole_0(X26,k1_tarski(X26)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 16.92/17.14  cnf(c_0_33, plain, (v3_ordinal1(k3_tarski(X1))|~v3_ordinal1(esk5_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 16.92/17.14  cnf(c_0_34, negated_conjecture, (v3_ordinal1(esk5_1(esk7_0))|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 16.92/17.14  cnf(c_0_35, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(k1_ordinal1(X1),esk7_0)|~v3_ordinal1(X1)|~r2_hidden(X1,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 16.92/17.14  cnf(c_0_36, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 16.92/17.14  cnf(c_0_37, negated_conjecture, (v3_ordinal1(k3_tarski(esk7_0))|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_30])).
% 16.92/17.14  fof(c_0_38, plain, ![X13, X14, X15, X17, X18, X19, X20, X22]:((((r2_hidden(X15,esk2_3(X13,X14,X15))|~r2_hidden(X15,X14)|X14!=k3_tarski(X13))&(r2_hidden(esk2_3(X13,X14,X15),X13)|~r2_hidden(X15,X14)|X14!=k3_tarski(X13)))&(~r2_hidden(X17,X18)|~r2_hidden(X18,X13)|r2_hidden(X17,X14)|X14!=k3_tarski(X13)))&((~r2_hidden(esk3_2(X19,X20),X20)|(~r2_hidden(esk3_2(X19,X20),X22)|~r2_hidden(X22,X19))|X20=k3_tarski(X19))&((r2_hidden(esk3_2(X19,X20),esk4_2(X19,X20))|r2_hidden(esk3_2(X19,X20),X20)|X20=k3_tarski(X19))&(r2_hidden(esk4_2(X19,X20),X19)|r2_hidden(esk3_2(X19,X20),X20)|X20=k3_tarski(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 16.92/17.14  cnf(c_0_39, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk7_0)|~v3_ordinal1(X1)|~r2_hidden(X1,esk7_0)), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 16.92/17.14  cnf(c_0_40, negated_conjecture, (k3_tarski(esk7_0)=esk7_0|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_22, c_0_37])).
% 16.92/17.14  fof(c_0_41, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 16.92/17.14  fof(c_0_42, plain, ![X37]:(~v3_ordinal1(X37)|v3_ordinal1(k1_ordinal1(X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 16.92/17.14  cnf(c_0_43, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 16.92/17.14  cnf(c_0_44, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk7_0)|~r2_hidden(X1,esk7_0)), inference(csr,[status(thm)],[c_0_39, c_0_30])).
% 16.92/17.14  cnf(c_0_45, negated_conjecture, (r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_40]), c_0_28])).
% 16.92/17.14  fof(c_0_46, plain, ![X30]:r2_hidden(X30,k1_ordinal1(X30)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 16.92/17.14  fof(c_0_47, plain, ![X47, X48]:(~r2_hidden(X47,X48)|~r1_tarski(X48,X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 16.92/17.14  cnf(c_0_48, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 16.92/17.14  cnf(c_0_49, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 16.92/17.14  cnf(c_0_50, plain, (r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X3,X2)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_43])).
% 16.92/17.14  cnf(c_0_51, negated_conjecture, (r2_hidden(k2_xboole_0(k3_tarski(esk7_0),k1_tarski(k3_tarski(esk7_0))),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_28])).
% 16.92/17.14  cnf(c_0_52, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 16.92/17.14  cnf(c_0_53, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 16.92/17.14  cnf(c_0_54, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_48])).
% 16.92/17.14  fof(c_0_55, plain, ![X40, X41]:((~r2_hidden(X40,k1_ordinal1(X41))|r1_ordinal1(X40,X41)|~v3_ordinal1(X41)|~v3_ordinal1(X40))&(~r1_ordinal1(X40,X41)|r2_hidden(X40,k1_ordinal1(X41))|~v3_ordinal1(X41)|~v3_ordinal1(X40))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).
% 16.92/17.14  cnf(c_0_56, plain, (v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_49, c_0_36])).
% 16.92/17.14  fof(c_0_57, plain, ![X31, X32]:((~r2_hidden(X31,k1_ordinal1(X32))|(r2_hidden(X31,X32)|X31=X32))&((~r2_hidden(X31,X32)|r2_hidden(X31,k1_ordinal1(X32)))&(X31!=X32|r2_hidden(X31,k1_ordinal1(X32))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).
% 16.92/17.14  cnf(c_0_58, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|X2!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 16.92/17.14  cnf(c_0_59, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(X1,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)|~r2_hidden(X1,k2_xboole_0(k3_tarski(esk7_0),k1_tarski(k3_tarski(esk7_0))))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 16.92/17.14  cnf(c_0_60, plain, (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_52, c_0_36])).
% 16.92/17.14  cnf(c_0_61, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 16.92/17.14  cnf(c_0_62, plain, (r1_ordinal1(X1,X2)|~r2_hidden(X1,k1_ordinal1(X2))|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 16.92/17.14  cnf(c_0_63, negated_conjecture, (v3_ordinal1(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(spm,[status(thm)],[c_0_56, c_0_19])).
% 16.92/17.14  cnf(c_0_64, plain, (r2_hidden(X1,k1_ordinal1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 16.92/17.14  cnf(c_0_65, plain, (r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)|~r2_hidden(X2,k3_tarski(X1))), inference(er,[status(thm)],[c_0_58])).
% 16.92/17.14  cnf(c_0_66, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])).
% 16.92/17.14  fof(c_0_67, plain, ![X28, X29]:((~r1_ordinal1(X28,X29)|r1_tarski(X28,X29)|(~v3_ordinal1(X28)|~v3_ordinal1(X29)))&(~r1_tarski(X28,X29)|r1_ordinal1(X28,X29)|(~v3_ordinal1(X28)|~v3_ordinal1(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 16.92/17.14  cnf(c_0_68, plain, (r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_62, c_0_36])).
% 16.92/17.14  cnf(c_0_69, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(spm,[status(thm)],[c_0_27, c_0_63])).
% 16.92/17.14  cnf(c_0_70, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_64, c_0_36])).
% 16.92/17.14  cnf(c_0_71, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 16.92/17.14  cnf(c_0_72, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 16.92/17.14  cnf(c_0_73, negated_conjecture, (r1_ordinal1(X1,esk7_0)|~r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_19]), c_0_69])).
% 16.92/17.14  cnf(c_0_74, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 16.92/17.14  cnf(c_0_75, plain, (r2_hidden(X1,esk2_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k3_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 16.92/17.14  cnf(c_0_76, negated_conjecture, (r1_tarski(X1,esk7_0)|~r1_ordinal1(X1,esk7_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_72, c_0_19])).
% 16.92/17.14  cnf(c_0_77, negated_conjecture, (v3_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_30, c_0_71])).
% 16.92/17.14  cnf(c_0_78, negated_conjecture, (r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 16.92/17.14  cnf(c_0_79, plain, (r2_hidden(X1,esk2_3(X2,k3_tarski(X2),X1))|~r2_hidden(X1,k3_tarski(X2))), inference(er,[status(thm)],[c_0_75])).
% 16.92/17.14  cnf(c_0_80, negated_conjecture, (r2_hidden(esk8_0,esk7_0)|r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78])).
% 16.92/17.14  cnf(c_0_81, negated_conjecture, (r2_hidden(esk7_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_79, c_0_66])).
% 16.92/17.14  cnf(c_0_82, negated_conjecture, (r2_hidden(esk8_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_80]), c_0_81])).
% 16.92/17.14  cnf(c_0_83, plain, (X1=k3_tarski(X1)|~v4_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 16.92/17.14  cnf(c_0_84, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_44, c_0_82])).
% 16.92/17.14  cnf(c_0_85, negated_conjecture, (k3_tarski(esk7_0)=esk7_0|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 16.92/17.14  fof(c_0_86, plain, ![X38, X39]:((~r2_hidden(X38,X39)|r1_ordinal1(k1_ordinal1(X38),X39)|~v3_ordinal1(X39)|~v3_ordinal1(X38))&(~r1_ordinal1(k1_ordinal1(X38),X39)|r2_hidden(X38,X39)|~v3_ordinal1(X39)|~v3_ordinal1(X38))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_ordinal1])])])])).
% 16.92/17.14  cnf(c_0_87, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|r2_hidden(esk2_3(esk7_0,esk7_0,X1),esk7_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_65, c_0_85])).
% 16.92/17.14  cnf(c_0_88, plain, (r1_ordinal1(k1_ordinal1(X1),X2)|~r2_hidden(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 16.92/17.14  cnf(c_0_89, negated_conjecture, (r2_hidden(esk2_3(esk7_0,esk7_0,esk8_0),esk7_0)|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_87, c_0_82])).
% 16.92/17.14  cnf(c_0_90, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|r2_hidden(X1,esk2_3(esk7_0,esk7_0,X1))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_79, c_0_85])).
% 16.92/17.14  cnf(c_0_91, plain, (r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_88, c_0_36])).
% 16.92/17.14  cnf(c_0_92, negated_conjecture, (r2_hidden(esk2_3(esk7_0,esk7_0,esk8_0),esk7_0)|r2_hidden(X1,k3_tarski(esk7_0))|~r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_50, c_0_89])).
% 16.92/17.14  cnf(c_0_93, negated_conjecture, (r2_hidden(esk8_0,esk2_3(esk7_0,esk7_0,esk8_0))|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_90, c_0_82])).
% 16.92/17.14  cnf(c_0_94, plain, (r2_hidden(X1,k1_ordinal1(X2))|~r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 16.92/17.14  cnf(c_0_95, plain, (r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_91, c_0_27])).
% 16.92/17.14  cnf(c_0_96, negated_conjecture, (r2_hidden(esk2_3(esk7_0,esk7_0,esk8_0),esk7_0)|r2_hidden(esk8_0,k3_tarski(esk7_0))), inference(spm,[status(thm)],[c_0_92, c_0_60])).
% 16.92/17.14  cnf(c_0_97, negated_conjecture, (r2_hidden(esk8_0,esk2_3(esk7_0,esk7_0,esk8_0))|r2_hidden(X1,k3_tarski(esk7_0))|~r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_50, c_0_93])).
% 16.92/17.14  cnf(c_0_98, negated_conjecture, (v3_ordinal1(esk8_0)), inference(spm,[status(thm)],[c_0_30, c_0_82])).
% 16.92/17.14  cnf(c_0_99, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r1_ordinal1(X1,X2)), inference(rw,[status(thm)],[c_0_94, c_0_36])).
% 16.92/17.14  cnf(c_0_100, negated_conjecture, (r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),esk7_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_95, c_0_19])).
% 16.92/17.14  cnf(c_0_101, negated_conjecture, (r2_hidden(esk8_0,k3_tarski(esk7_0))|r2_hidden(X1,k3_tarski(esk7_0))|~r2_hidden(X1,esk2_3(esk7_0,esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_50, c_0_96])).
% 16.92/17.14  cnf(c_0_102, negated_conjecture, (r2_hidden(esk8_0,esk2_3(esk7_0,esk7_0,esk8_0))|r2_hidden(esk8_0,k3_tarski(esk7_0))), inference(spm,[status(thm)],[c_0_97, c_0_60])).
% 16.92/17.14  cnf(c_0_103, negated_conjecture, (v3_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_56, c_0_98])).
% 16.92/17.14  cnf(c_0_104, plain, (r2_hidden(X1,X2)|X1=X2|~r2_hidden(X1,k1_ordinal1(X2))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 16.92/17.14  cnf(c_0_105, negated_conjecture, (r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))|~r1_ordinal1(X1,esk7_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_99, c_0_19])).
% 16.92/17.14  cnf(c_0_106, negated_conjecture, (r1_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_100, c_0_82])).
% 16.92/17.14  cnf(c_0_107, negated_conjecture, (r2_hidden(esk8_0,k3_tarski(esk7_0))), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 16.92/17.14  cnf(c_0_108, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_27, c_0_103])).
% 16.92/17.14  cnf(c_0_109, plain, (X1=X2|r2_hidden(X1,X2)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_104, c_0_36])).
% 16.92/17.14  cnf(c_0_110, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_103]), c_0_106])])).
% 16.92/17.14  cnf(c_0_111, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk7_0)), inference(spm,[status(thm)],[c_0_65, c_0_107])).
% 16.92/17.14  cnf(c_0_112, negated_conjecture, (r1_ordinal1(X1,esk8_0)|~r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_98]), c_0_108])).
% 16.92/17.14  cnf(c_0_113, negated_conjecture, (k2_xboole_0(esk8_0,k1_tarski(esk8_0))=esk7_0|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_109, c_0_110])).
% 16.92/17.14  cnf(c_0_114, negated_conjecture, (r1_tarski(X1,esk8_0)|~r1_ordinal1(X1,esk8_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_72, c_0_98])).
% 16.92/17.14  cnf(c_0_115, negated_conjecture, (v3_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0))), inference(spm,[status(thm)],[c_0_30, c_0_111])).
% 16.92/17.14  cnf(c_0_116, negated_conjecture, (r1_ordinal1(X1,esk8_0)|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 16.92/17.14  cnf(c_0_117, negated_conjecture, (~r2_hidden(k1_ordinal1(esk8_0),esk7_0)|~v4_ordinal1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 16.92/17.14  cnf(c_0_118, negated_conjecture, (r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)|~r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_114, c_0_115])).
% 16.92/17.14  cnf(c_0_119, negated_conjecture, (r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_116, c_0_111])).
% 16.92/17.14  cnf(c_0_120, negated_conjecture, (~v4_ordinal1(esk7_0)|~r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(rw,[status(thm)],[c_0_117, c_0_36])).
% 16.92/17.14  cnf(c_0_121, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_118, c_0_119])).
% 16.92/17.14  cnf(c_0_122, negated_conjecture, (r2_hidden(esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0))), inference(spm,[status(thm)],[c_0_79, c_0_107])).
% 16.92/17.14  cnf(c_0_123, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk5_1(esk7_0),esk7_0)|~r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_120, c_0_29])).
% 16.92/17.14  cnf(c_0_124, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_121]), c_0_122])])).
% 16.92/17.14  cnf(c_0_125, negated_conjecture, (r2_hidden(esk5_1(esk7_0),esk7_0)|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_123, c_0_124])])).
% 16.92/17.14  cnf(c_0_126, negated_conjecture, (v3_ordinal1(esk5_1(esk7_0))|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(k3_tarski(esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_30, c_0_125])).
% 16.92/17.14  cnf(c_0_127, negated_conjecture, (v3_ordinal1(k3_tarski(esk7_0))|r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_126]), c_0_30])).
% 16.92/17.14  cnf(c_0_128, negated_conjecture, (k3_tarski(esk7_0)=esk7_0|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(k3_tarski(esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_22, c_0_127])).
% 16.92/17.14  cnf(c_0_129, negated_conjecture, (~v4_ordinal1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_120, c_0_124])])).
% 16.92/17.14  cnf(c_0_130, negated_conjecture, (r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_128]), c_0_129])).
% 16.92/17.14  cnf(c_0_131, negated_conjecture, (r2_hidden(k2_xboole_0(k3_tarski(esk7_0),k1_tarski(k3_tarski(esk7_0))),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_130]), c_0_129])).
% 16.92/17.14  cnf(c_0_132, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(X1,k3_tarski(esk7_0))|~r2_hidden(X1,k2_xboole_0(k3_tarski(esk7_0),k1_tarski(k3_tarski(esk7_0))))), inference(spm,[status(thm)],[c_0_50, c_0_131])).
% 16.92/17.14  cnf(c_0_133, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_60]), c_0_61])).
% 16.92/17.15  cnf(c_0_134, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_65, c_0_133])).
% 16.92/17.15  cnf(c_0_135, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(spm,[status(thm)],[c_0_70, c_0_134])).
% 16.92/17.15  cnf(c_0_136, negated_conjecture, (v3_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0))), inference(spm,[status(thm)],[c_0_30, c_0_134])).
% 16.92/17.15  cnf(c_0_137, negated_conjecture, (r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_73, c_0_135])).
% 16.92/17.15  cnf(c_0_138, negated_conjecture, (r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_136]), c_0_137])])).
% 16.92/17.15  cnf(c_0_139, negated_conjecture, (r2_hidden(esk7_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk7_0))), inference(spm,[status(thm)],[c_0_79, c_0_133])).
% 16.92/17.15  cnf(c_0_140, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_138]), c_0_139])]), ['proof']).
% 16.92/17.15  # SZS output end CNFRefutation
% 16.92/17.15  # Proof object total steps             : 141
% 16.92/17.15  # Proof object clause steps            : 110
% 16.92/17.15  # Proof object formula steps           : 31
% 16.92/17.15  # Proof object conjectures             : 80
% 16.92/17.15  # Proof object clause conjectures      : 77
% 16.92/17.15  # Proof object formula conjectures     : 3
% 16.92/17.15  # Proof object initial clauses used    : 24
% 16.92/17.15  # Proof object initial formulas used   : 15
% 16.92/17.15  # Proof object generating inferences   : 69
% 16.92/17.15  # Proof object simplifying inferences  : 40
% 16.92/17.15  # Training examples: 0 positive, 0 negative
% 16.92/17.15  # Parsed axioms                        : 18
% 16.92/17.15  # Removed by relevancy pruning/SinE    : 0
% 16.92/17.15  # Initial clauses                      : 40
% 16.92/17.15  # Removed in clause preprocessing      : 1
% 16.92/17.15  # Initial clauses in saturation        : 39
% 16.92/17.15  # Processed clauses                    : 33031
% 16.92/17.15  # ...of these trivial                  : 596
% 16.92/17.15  # ...subsumed                          : 22839
% 16.92/17.15  # ...remaining for further processing  : 9596
% 16.92/17.15  # Other redundant clauses eliminated   : 52
% 16.92/17.15  # Clauses deleted for lack of memory   : 0
% 16.92/17.15  # Backward-subsumed                    : 1223
% 16.92/17.15  # Backward-rewritten                   : 2100
% 16.92/17.15  # Generated clauses                    : 1784660
% 16.92/17.15  # ...of the previous two non-trivial   : 1520121
% 16.92/17.15  # Contextual simplify-reflections      : 158
% 16.92/17.15  # Paramodulations                      : 1784559
% 16.92/17.15  # Factorizations                       : 22
% 16.92/17.15  # Equation resolutions                 : 52
% 16.92/17.15  # Propositional unsat checks           : 0
% 16.92/17.15  #    Propositional check models        : 0
% 16.92/17.15  #    Propositional check unsatisfiable : 0
% 16.92/17.15  #    Propositional clauses             : 0
% 16.92/17.15  #    Propositional clauses after purity: 0
% 16.92/17.15  #    Propositional unsat core size     : 0
% 16.92/17.15  #    Propositional preprocessing time  : 0.000
% 16.92/17.15  #    Propositional encoding time       : 0.000
% 16.92/17.15  #    Propositional solver time         : 0.000
% 16.92/17.15  #    Success case prop preproc time    : 0.000
% 16.92/17.15  #    Success case prop encoding time   : 0.000
% 16.92/17.15  #    Success case prop solver time     : 0.000
% 16.92/17.15  # Current number of processed clauses  : 6203
% 16.92/17.15  #    Positive orientable unit clauses  : 720
% 16.92/17.15  #    Positive unorientable unit clauses: 0
% 16.92/17.15  #    Negative unit clauses             : 173
% 16.92/17.15  #    Non-unit-clauses                  : 5310
% 16.92/17.15  # Current number of unprocessed clauses: 1481503
% 16.92/17.15  # ...number of literals in the above   : 7967524
% 16.92/17.15  # Current number of archived formulas  : 0
% 16.92/17.15  # Current number of archived clauses   : 3388
% 16.92/17.15  # Clause-clause subsumption calls (NU) : 5584511
% 16.92/17.15  # Rec. Clause-clause subsumption calls : 1719556
% 16.92/17.15  # Non-unit clause-clause subsumptions  : 15508
% 16.92/17.15  # Unit Clause-clause subsumption calls : 386334
% 16.92/17.15  # Rewrite failures with RHS unbound    : 0
% 16.92/17.15  # BW rewrite match attempts            : 2306
% 16.92/17.15  # BW rewrite match successes           : 167
% 16.92/17.15  # Condensation attempts                : 0
% 16.92/17.15  # Condensation successes               : 0
% 16.92/17.15  # Termbank termtop insertions          : 53007692
% 17.02/17.21  
% 17.02/17.21  # -------------------------------------------------
% 17.02/17.21  # User time                : 16.304 s
% 17.02/17.21  # System time              : 0.554 s
% 17.02/17.21  # Total time               : 16.858 s
% 17.02/17.21  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
