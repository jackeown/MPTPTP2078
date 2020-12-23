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
% DateTime   : Thu Dec  3 10:56:15 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 336 expanded)
%              Number of clauses        :   43 ( 141 expanded)
%              Number of leaves         :   12 (  84 expanded)
%              Depth                    :   10
%              Number of atoms          :  219 (1121 expanded)
%              Number of equality atoms :   41 ( 123 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
          <=> r1_ordinal1(k1_ordinal1(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(t13_ordinal1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,k1_ordinal1(X2))
    <=> ( r2_hidden(X1,X2)
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(t26_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r1_ordinal1(X1,X2)
            | r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(connectedness_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
        | r1_ordinal1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(t29_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k1_ordinal1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X1,X2)
            <=> r1_ordinal1(k1_ordinal1(X1),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t33_ordinal1])).

fof(c_0_13,negated_conjecture,
    ( v3_ordinal1(esk3_0)
    & v3_ordinal1(esk4_0)
    & ( ~ r2_hidden(esk3_0,esk4_0)
      | ~ r1_ordinal1(k1_ordinal1(esk3_0),esk4_0) )
    & ( r2_hidden(esk3_0,esk4_0)
      | r1_ordinal1(k1_ordinal1(esk3_0),esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_14,plain,(
    ! [X30] : k1_ordinal1(X30) = k2_xboole_0(X30,k1_tarski(X30)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_15,plain,(
    ! [X18,X19] :
      ( ( r1_tarski(X18,X19)
        | X18 != X19 )
      & ( r1_tarski(X19,X18)
        | X18 != X19 )
      & ( ~ r1_tarski(X18,X19)
        | ~ r1_tarski(X19,X18)
        | X18 = X19 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_16,plain,(
    ! [X31,X32] :
      ( ( ~ r1_ordinal1(X31,X32)
        | r1_tarski(X31,X32)
        | ~ v3_ordinal1(X31)
        | ~ v3_ordinal1(X32) )
      & ( ~ r1_tarski(X31,X32)
        | r1_ordinal1(X31,X32)
        | ~ v3_ordinal1(X31)
        | ~ v3_ordinal1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

fof(c_0_17,plain,(
    ! [X33,X34] :
      ( ( ~ r2_hidden(X33,k1_ordinal1(X34))
        | r2_hidden(X33,X34)
        | X33 = X34 )
      & ( ~ r2_hidden(X33,X34)
        | r2_hidden(X33,k1_ordinal1(X34)) )
      & ( X33 != X34
        | r2_hidden(X33,k1_ordinal1(X34)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).

cnf(c_0_18,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk4_0)
    | ~ r1_ordinal1(k1_ordinal1(esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X37,X38] :
      ( ~ v3_ordinal1(X37)
      | ~ v3_ordinal1(X38)
      | r1_ordinal1(X37,X38)
      | r2_hidden(X38,X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).

fof(c_0_21,plain,(
    ! [X40,X41] :
      ( ~ r2_hidden(X40,X41)
      | ~ r1_tarski(X41,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_22,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_24,plain,(
    ! [X28,X29] :
      ( ~ v3_ordinal1(X28)
      | ~ v3_ordinal1(X29)
      | r1_ordinal1(X28,X29)
      | r1_ordinal1(X29,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | ~ r2_hidden(X1,k1_ordinal1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk4_0)
    | ~ r1_ordinal1(k2_xboole_0(esk3_0,k1_tarski(esk3_0)),esk4_0) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( r1_ordinal1(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( v3_ordinal1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_29,plain,(
    ! [X5,X6] :
      ( ~ r2_hidden(X5,X6)
      | ~ r2_hidden(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

fof(c_0_30,plain,(
    ! [X39] :
      ( ~ v3_ordinal1(X39)
      | v3_ordinal1(k1_ordinal1(X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r1_ordinal1(k1_ordinal1(esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_33,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( ~ r2_hidden(X10,X9)
        | r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X9)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X14)
        | r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k2_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_34,plain,
    ( X1 = X2
    | ~ r1_ordinal1(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_35,plain,
    ( r1_ordinal1(X1,X2)
    | r1_ordinal1(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_19])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk4_0,k2_xboole_0(esk3_0,k1_tarski(esk3_0)))
    | ~ v3_ordinal1(k2_xboole_0(esk3_0,k1_tarski(esk3_0)))
    | ~ r2_hidden(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_23])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r1_ordinal1(k2_xboole_0(esk3_0,k1_tarski(esk3_0)),esk4_0) ),
    inference(rw,[status(thm)],[c_0_32,c_0_19])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( X1 = X2
    | ~ r1_ordinal1(X2,X1)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_23])).

cnf(c_0_45,negated_conjecture,
    ( r1_ordinal1(esk4_0,X1)
    | r1_ordinal1(X1,esk4_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_28])).

cnf(c_0_46,negated_conjecture,
    ( v3_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_47,negated_conjecture,
    ( esk3_0 = esk4_0
    | ~ v3_ordinal1(k2_xboole_0(esk3_0,k1_tarski(esk3_0)))
    | ~ r2_hidden(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_48,plain,
    ( v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[c_0_39,c_0_19])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | ~ v3_ordinal1(k2_xboole_0(esk3_0,k1_tarski(esk3_0)))
    | ~ r2_hidden(esk4_0,k2_xboole_0(esk3_0,k1_tarski(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_28])])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_42,c_0_19])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_27])).

cnf(c_0_53,negated_conjecture,
    ( r1_ordinal1(esk3_0,esk4_0)
    | r1_ordinal1(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( esk3_0 = esk4_0
    | ~ r2_hidden(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_46])])).

cnf(c_0_55,negated_conjecture,
    ( ~ v3_ordinal1(k2_xboole_0(esk3_0,k1_tarski(esk3_0)))
    | ~ r2_hidden(esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_38])).

fof(c_0_56,plain,(
    ! [X20,X21,X22,X23,X24,X25] :
      ( ( ~ r2_hidden(X22,X21)
        | X22 = X20
        | X21 != k1_tarski(X20) )
      & ( X23 != X20
        | r2_hidden(X23,X21)
        | X21 != k1_tarski(X20) )
      & ( ~ r2_hidden(esk2_2(X24,X25),X25)
        | esk2_2(X24,X25) != X24
        | X25 = k1_tarski(X24) )
      & ( r2_hidden(esk2_2(X24,X25),X25)
        | esk2_2(X24,X25) = X24
        | X25 = k1_tarski(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | ~ v3_ordinal1(k2_xboole_0(esk3_0,k1_tarski(esk3_0)))
    | ~ r2_hidden(esk4_0,k1_tarski(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( esk3_0 = esk4_0
    | r1_ordinal1(esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_46]),c_0_28])]),c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_48]),c_0_46])])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | ~ r2_hidden(esk4_0,k1_tarski(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_48]),c_0_46])])).

cnf(c_0_64,negated_conjecture,
    ( esk3_0 = esk4_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_59]),c_0_28]),c_0_46])]),c_0_60])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_61])])).

cnf(c_0_66,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64]),c_0_64]),c_0_65])]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:57:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.14/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t33_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)<=>r1_ordinal1(k1_ordinal1(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 0.14/0.38  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.14/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.14/0.38  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.14/0.38  fof(t13_ordinal1, axiom, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 0.14/0.38  fof(t26_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r1_ordinal1(X1,X2)|r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 0.14/0.38  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.14/0.38  fof(connectedness_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 0.14/0.38  fof(antisymmetry_r2_hidden, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 0.14/0.38  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 0.14/0.38  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.14/0.38  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.14/0.38  fof(c_0_12, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)<=>r1_ordinal1(k1_ordinal1(X1),X2))))), inference(assume_negation,[status(cth)],[t33_ordinal1])).
% 0.14/0.38  fof(c_0_13, negated_conjecture, (v3_ordinal1(esk3_0)&(v3_ordinal1(esk4_0)&((~r2_hidden(esk3_0,esk4_0)|~r1_ordinal1(k1_ordinal1(esk3_0),esk4_0))&(r2_hidden(esk3_0,esk4_0)|r1_ordinal1(k1_ordinal1(esk3_0),esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.14/0.38  fof(c_0_14, plain, ![X30]:k1_ordinal1(X30)=k2_xboole_0(X30,k1_tarski(X30)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.14/0.38  fof(c_0_15, plain, ![X18, X19]:(((r1_tarski(X18,X19)|X18!=X19)&(r1_tarski(X19,X18)|X18!=X19))&(~r1_tarski(X18,X19)|~r1_tarski(X19,X18)|X18=X19)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.14/0.38  fof(c_0_16, plain, ![X31, X32]:((~r1_ordinal1(X31,X32)|r1_tarski(X31,X32)|(~v3_ordinal1(X31)|~v3_ordinal1(X32)))&(~r1_tarski(X31,X32)|r1_ordinal1(X31,X32)|(~v3_ordinal1(X31)|~v3_ordinal1(X32)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.14/0.38  fof(c_0_17, plain, ![X33, X34]:((~r2_hidden(X33,k1_ordinal1(X34))|(r2_hidden(X33,X34)|X33=X34))&((~r2_hidden(X33,X34)|r2_hidden(X33,k1_ordinal1(X34)))&(X33!=X34|r2_hidden(X33,k1_ordinal1(X34))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).
% 0.14/0.38  cnf(c_0_18, negated_conjecture, (~r2_hidden(esk3_0,esk4_0)|~r1_ordinal1(k1_ordinal1(esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_19, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  fof(c_0_20, plain, ![X37, X38]:(~v3_ordinal1(X37)|(~v3_ordinal1(X38)|(r1_ordinal1(X37,X38)|r2_hidden(X38,X37)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).
% 0.14/0.38  fof(c_0_21, plain, ![X40, X41]:(~r2_hidden(X40,X41)|~r1_tarski(X41,X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.14/0.38  cnf(c_0_22, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_23, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  fof(c_0_24, plain, ![X28, X29]:(~v3_ordinal1(X28)|~v3_ordinal1(X29)|(r1_ordinal1(X28,X29)|r1_ordinal1(X29,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).
% 0.14/0.38  cnf(c_0_25, plain, (r2_hidden(X1,X2)|X1=X2|~r2_hidden(X1,k1_ordinal1(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (~r2_hidden(esk3_0,esk4_0)|~r1_ordinal1(k2_xboole_0(esk3_0,k1_tarski(esk3_0)),esk4_0)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.14/0.38  cnf(c_0_27, plain, (r1_ordinal1(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (v3_ordinal1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  fof(c_0_29, plain, ![X5, X6]:(~r2_hidden(X5,X6)|~r2_hidden(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).
% 0.14/0.38  fof(c_0_30, plain, ![X39]:(~v3_ordinal1(X39)|v3_ordinal1(k1_ordinal1(X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 0.14/0.38  cnf(c_0_31, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|r1_ordinal1(k1_ordinal1(esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  fof(c_0_33, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:(((~r2_hidden(X10,X9)|(r2_hidden(X10,X7)|r2_hidden(X10,X8))|X9!=k2_xboole_0(X7,X8))&((~r2_hidden(X11,X7)|r2_hidden(X11,X9)|X9!=k2_xboole_0(X7,X8))&(~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k2_xboole_0(X7,X8))))&(((~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_xboole_0(X12,X13)))&(r2_hidden(esk1_3(X12,X13,X14),X14)|(r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k2_xboole_0(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.14/0.38  cnf(c_0_34, plain, (X1=X2|~r1_ordinal1(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.14/0.38  cnf(c_0_35, plain, (r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.38  cnf(c_0_36, plain, (X1=X2|r2_hidden(X1,X2)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_25, c_0_19])).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, (r2_hidden(esk4_0,k2_xboole_0(esk3_0,k1_tarski(esk3_0)))|~v3_ordinal1(k2_xboole_0(esk3_0,k1_tarski(esk3_0)))|~r2_hidden(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.14/0.38  cnf(c_0_38, plain, (~r2_hidden(X1,X2)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.38  cnf(c_0_39, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.38  cnf(c_0_40, plain, (~r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_31, c_0_23])).
% 0.14/0.38  cnf(c_0_41, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|r1_ordinal1(k2_xboole_0(esk3_0,k1_tarski(esk3_0)),esk4_0)), inference(rw,[status(thm)],[c_0_32, c_0_19])).
% 0.14/0.38  cnf(c_0_42, plain, (r2_hidden(X1,k1_ordinal1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.38  cnf(c_0_43, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.38  cnf(c_0_44, plain, (X1=X2|~r1_ordinal1(X2,X1)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(spm,[status(thm)],[c_0_34, c_0_23])).
% 0.14/0.38  cnf(c_0_45, negated_conjecture, (r1_ordinal1(esk4_0,X1)|r1_ordinal1(X1,esk4_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_35, c_0_28])).
% 0.14/0.38  cnf(c_0_46, negated_conjecture, (v3_ordinal1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_47, negated_conjecture, (esk3_0=esk4_0|~v3_ordinal1(k2_xboole_0(esk3_0,k1_tarski(esk3_0)))|~r2_hidden(esk3_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 0.14/0.38  cnf(c_0_48, plain, (v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_39, c_0_19])).
% 0.14/0.38  cnf(c_0_49, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|~v3_ordinal1(k2_xboole_0(esk3_0,k1_tarski(esk3_0)))|~r2_hidden(esk4_0,k2_xboole_0(esk3_0,k1_tarski(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_28])])).
% 0.14/0.38  cnf(c_0_50, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_42, c_0_19])).
% 0.14/0.38  cnf(c_0_51, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_43])).
% 0.14/0.38  cnf(c_0_52, plain, (X1=X2|r2_hidden(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(spm,[status(thm)],[c_0_44, c_0_27])).
% 0.14/0.38  cnf(c_0_53, negated_conjecture, (r1_ordinal1(esk3_0,esk4_0)|r1_ordinal1(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.14/0.38  cnf(c_0_54, negated_conjecture, (esk3_0=esk4_0|~r2_hidden(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_46])])).
% 0.14/0.38  cnf(c_0_55, negated_conjecture, (~v3_ordinal1(k2_xboole_0(esk3_0,k1_tarski(esk3_0)))|~r2_hidden(esk4_0,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_38])).
% 0.14/0.38  fof(c_0_56, plain, ![X20, X21, X22, X23, X24, X25]:(((~r2_hidden(X22,X21)|X22=X20|X21!=k1_tarski(X20))&(X23!=X20|r2_hidden(X23,X21)|X21!=k1_tarski(X20)))&((~r2_hidden(esk2_2(X24,X25),X25)|esk2_2(X24,X25)!=X24|X25=k1_tarski(X24))&(r2_hidden(esk2_2(X24,X25),X25)|esk2_2(X24,X25)=X24|X25=k1_tarski(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.14/0.38  cnf(c_0_57, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_58, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|~v3_ordinal1(k2_xboole_0(esk3_0,k1_tarski(esk3_0)))|~r2_hidden(esk4_0,k1_tarski(esk3_0))), inference(spm,[status(thm)],[c_0_49, c_0_51])).
% 0.14/0.38  cnf(c_0_59, negated_conjecture, (esk3_0=esk4_0|r1_ordinal1(esk4_0,esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_46]), c_0_28])]), c_0_54])).
% 0.14/0.38  cnf(c_0_60, negated_conjecture, (~r2_hidden(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_48]), c_0_46])])).
% 0.14/0.38  cnf(c_0_61, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.14/0.38  cnf(c_0_62, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_57])).
% 0.14/0.38  cnf(c_0_63, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|~r2_hidden(esk4_0,k1_tarski(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_48]), c_0_46])])).
% 0.14/0.38  cnf(c_0_64, negated_conjecture, (esk3_0=esk4_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_59]), c_0_28]), c_0_46])]), c_0_60])).
% 0.14/0.38  cnf(c_0_65, plain, (r2_hidden(X1,k1_tarski(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_61])])).
% 0.14/0.38  cnf(c_0_66, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_31, c_0_62])).
% 0.14/0.38  cnf(c_0_67, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64]), c_0_64]), c_0_65])]), c_0_66]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 68
% 0.14/0.38  # Proof object clause steps            : 43
% 0.14/0.38  # Proof object formula steps           : 25
% 0.14/0.38  # Proof object conjectures             : 22
% 0.14/0.38  # Proof object clause conjectures      : 19
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 17
% 0.14/0.38  # Proof object initial formulas used   : 12
% 0.14/0.38  # Proof object generating inferences   : 17
% 0.14/0.38  # Proof object simplifying inferences  : 34
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 15
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 34
% 0.14/0.38  # Removed in clause preprocessing      : 1
% 0.14/0.38  # Initial clauses in saturation        : 33
% 0.14/0.38  # Processed clauses                    : 245
% 0.14/0.38  # ...of these trivial                  : 3
% 0.14/0.38  # ...subsumed                          : 82
% 0.14/0.38  # ...remaining for further processing  : 160
% 0.14/0.38  # Other redundant clauses eliminated   : 10
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 7
% 0.14/0.38  # Backward-rewritten                   : 26
% 0.14/0.38  # Generated clauses                    : 566
% 0.14/0.38  # ...of the previous two non-trivial   : 541
% 0.14/0.38  # Contextual simplify-reflections      : 6
% 0.14/0.38  # Paramodulations                      : 537
% 0.14/0.38  # Factorizations                       : 20
% 0.14/0.38  # Equation resolutions                 : 10
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 118
% 0.14/0.38  #    Positive orientable unit clauses  : 7
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 61
% 0.14/0.38  #    Non-unit-clauses                  : 50
% 0.14/0.38  # Current number of unprocessed clauses: 308
% 0.14/0.38  # ...number of literals in the above   : 604
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 34
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 1169
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 774
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 30
% 0.14/0.38  # Unit Clause-clause subsumption calls : 1159
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 46
% 0.14/0.38  # BW rewrite match successes           : 3
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 8270
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.040 s
% 0.14/0.38  # System time              : 0.004 s
% 0.14/0.38  # Total time               : 0.045 s
% 0.14/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
