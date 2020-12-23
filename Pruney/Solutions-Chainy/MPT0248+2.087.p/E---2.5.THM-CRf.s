%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:51 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  129 (3171205 expanded)
%              Number of clauses        :   98 (1346937 expanded)
%              Number of leaves         :   15 (881052 expanded)
%              Depth                    :   44
%              Number of atoms          :  280 (5695636 expanded)
%              Number of equality atoms :  102 (4289085 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t43_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_xboole_0
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_xboole_0
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t43_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X43,X44] : k3_tarski(k2_tarski(X43,X44)) = k2_xboole_0(X43,X44) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_17,plain,(
    ! [X34,X35] : k1_enumset1(X34,X34,X35) = k2_tarski(X34,X35) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,negated_conjecture,
    ( k1_tarski(esk5_0) = k2_xboole_0(esk6_0,esk7_0)
    & ( esk6_0 != k1_tarski(esk5_0)
      | esk7_0 != k1_tarski(esk5_0) )
    & ( esk6_0 != k1_xboole_0
      | esk7_0 != k1_tarski(esk5_0) )
    & ( esk6_0 != k1_tarski(esk5_0)
      | esk7_0 != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_19,plain,(
    ! [X33] : k2_tarski(X33,X33) = k1_tarski(X33) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_20,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X36,X37,X38] : k2_enumset1(X36,X36,X37,X38) = k1_enumset1(X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_23,plain,(
    ! [X39,X40,X41,X42] : k3_enumset1(X39,X39,X40,X41,X42) = k2_enumset1(X39,X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_24,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_tarski(X19,X20)
      | r1_tarski(X19,k2_xboole_0(X21,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

fof(c_0_25,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_26,plain,(
    ! [X22,X23] :
      ( ~ r1_tarski(X22,X23)
      | k2_xboole_0(X22,X23) = X23 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_27,negated_conjecture,
    ( k1_tarski(esk5_0) = k2_xboole_0(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_30,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_32,plain,(
    ! [X15] :
      ( X15 = k1_xboole_0
      | r2_hidden(esk3_1(X15),X15) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_21]),c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,k1_xboole_0)) = k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)
    | r2_hidden(esk3_1(esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_42,plain,(
    ! [X26,X27,X28,X29,X30,X31] :
      ( ( ~ r2_hidden(X28,X27)
        | X28 = X26
        | X27 != k1_tarski(X26) )
      & ( X29 != X26
        | r2_hidden(X29,X27)
        | X27 != k1_tarski(X26) )
      & ( ~ r2_hidden(esk4_2(X30,X31),X31)
        | esk4_2(X30,X31) != X30
        | X31 = k1_tarski(X30) )
      & ( r2_hidden(esk4_2(X30,X31),X31)
        | esk4_2(X30,X31) = X30
        | X31 = k1_tarski(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_43,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( esk6_0 != k1_tarski(esk5_0)
    | esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_46,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_40,c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,X1)) = k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)
    | r2_hidden(esk3_1(esk7_0),esk7_0)
    | r2_hidden(esk3_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_37])).

fof(c_0_48,plain,(
    ! [X24,X25] : r1_tarski(X24,k2_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_49,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk7_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_36])).

cnf(c_0_52,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | esk6_0 != k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_28]),c_0_21]),c_0_30]),c_0_31])).

cnf(c_0_53,negated_conjecture,
    ( k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = esk6_0
    | r2_hidden(esk3_1(esk6_0),esk6_0)
    | r2_hidden(esk3_1(esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,plain,
    ( X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_28]),c_0_21]),c_0_30]),c_0_31])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk3_1(esk7_0),esk7_0)
    | r2_hidden(esk3_1(esk6_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_37])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_59,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk3_1(esk7_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | r2_hidden(esk3_1(esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_36])).

cnf(c_0_62,negated_conjecture,
    ( esk3_1(esk7_0) = esk5_0
    | r2_hidden(esk3_1(esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk3_1(esk6_0),esk6_0)
    | r2_hidden(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_62])).

fof(c_0_65,plain,(
    ! [X45,X46,X47] :
      ( ( r2_hidden(X45,X47)
        | ~ r1_tarski(k2_tarski(X45,X46),X47) )
      & ( r2_hidden(X46,X47)
        | ~ r1_tarski(k2_tarski(X45,X46),X47) )
      & ( ~ r2_hidden(X45,X47)
        | ~ r2_hidden(X46,X47)
        | r1_tarski(k2_tarski(X45,X46),X47) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk3_1(esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | r2_hidden(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_67,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( esk3_1(esk6_0) = esk5_0
    | r2_hidden(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_66])).

cnf(c_0_69,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_21]),c_0_30]),c_0_31])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0)
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,esk5_0),esk7_0)
    | r2_hidden(esk5_0,esk6_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_72,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk7_0)
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | esk7_0 != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_75,negated_conjecture,
    ( k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = esk7_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_51])])).

cnf(c_0_76,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | esk7_0 != k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_28]),c_0_21]),c_0_30]),c_0_31])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(esk6_0,esk7_0)
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0)
    | esk6_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_76,c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0)
    | r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk3_1(esk6_0),esk6_0)
    | r2_hidden(esk5_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_37])).

cnf(c_0_81,negated_conjecture,
    ( X1 = esk5_0
    | r2_hidden(esk5_0,esk6_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk3_1(esk6_0),esk7_0)
    | r2_hidden(esk5_0,k1_xboole_0)
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_83,negated_conjecture,
    ( esk3_1(esk6_0) = esk5_0
    | r2_hidden(esk5_0,k1_xboole_0)
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk5_0,k1_xboole_0)
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_83])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,esk5_0),esk6_0)
    | r2_hidden(esk5_0,k1_xboole_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_84])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)
    | r2_hidden(esk5_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_84])).

cnf(c_0_87,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_88,negated_conjecture,
    ( esk6_0 != k1_tarski(esk5_0)
    | esk7_0 != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_89,negated_conjecture,
    ( k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = esk6_0
    | r2_hidden(esk5_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_86]),c_0_61])])).

cnf(c_0_90,plain,
    ( X1 = X2
    | r2_hidden(esk2_2(X1,X2),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( esk6_0 != k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)
    | esk7_0 != k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_28]),c_0_28]),c_0_21]),c_0_21]),c_0_30]),c_0_30]),c_0_31]),c_0_31])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(esk7_0,esk6_0)
    | r2_hidden(esk5_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_89])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk5_0,k1_xboole_0)
    | esk7_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = esk7_0
    | r2_hidden(esk2_2(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk7_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_51])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk5_0,k1_xboole_0)
    | esk7_0 != esk6_0 ),
    inference(spm,[status(thm)],[c_0_91,c_0_89])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(esk5_0,k1_xboole_0)
    | r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_92])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(esk3_1(esk7_0),esk7_0)
    | r2_hidden(esk5_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_37])).

cnf(c_0_98,negated_conjecture,
    ( X1 = esk5_0
    | r2_hidden(esk5_0,k1_xboole_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_89])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(esk2_2(esk6_0,esk7_0),esk6_0)
    | r2_hidden(esk5_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_89]),c_0_95])).

cnf(c_0_100,negated_conjecture,
    ( r2_hidden(esk3_1(esk7_0),esk6_0)
    | r2_hidden(esk5_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_101,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_102,negated_conjecture,
    ( esk2_2(esk6_0,esk7_0) = esk5_0
    | r2_hidden(esk5_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_103,negated_conjecture,
    ( r2_hidden(esk5_0,k1_xboole_0)
    | ~ r1_tarski(esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_92]),c_0_95])).

fof(c_0_104,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_105,negated_conjecture,
    ( esk3_1(esk7_0) = esk5_0
    | r2_hidden(esk5_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_100])).

cnf(c_0_106,negated_conjecture,
    ( r2_hidden(esk5_0,k1_xboole_0)
    | ~ r2_hidden(esk5_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_103])).

cnf(c_0_107,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_108,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_109,negated_conjecture,
    ( r2_hidden(esk5_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_105]),c_0_106])).

cnf(c_0_110,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_111,negated_conjecture,
    ( r2_hidden(esk3_1(X1),X1)
    | r2_hidden(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_109,c_0_37])).

cnf(c_0_112,negated_conjecture,
    ( r2_hidden(esk1_1(X1),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_110])).

cnf(c_0_113,negated_conjecture,
    ( r2_hidden(esk1_1(esk7_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_112])).

cnf(c_0_114,negated_conjecture,
    ( esk1_1(esk7_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_113])).

cnf(c_0_115,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_112,c_0_114])).

cnf(c_0_116,negated_conjecture,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,esk5_0),esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_115])).

cnf(c_0_117,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_116,c_0_115])).

cnf(c_0_118,negated_conjecture,
    ( k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_117]),c_0_51])])).

cnf(c_0_119,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(rw,[status(thm)],[c_0_63,c_0_118])).

cnf(c_0_120,negated_conjecture,
    ( X1 = esk5_0
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_118])).

cnf(c_0_121,negated_conjecture,
    ( r2_hidden(esk1_1(esk6_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_119,c_0_112])).

cnf(c_0_122,negated_conjecture,
    ( esk1_1(esk6_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_120,c_0_121])).

cnf(c_0_123,negated_conjecture,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,esk1_1(X2)),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_69,c_0_112])).

cnf(c_0_124,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_112,c_0_122])).

cnf(c_0_125,negated_conjecture,
    ( r1_tarski(esk7_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_124]),c_0_122]),c_0_118])).

cnf(c_0_126,negated_conjecture,
    ( r1_tarski(esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_61,c_0_118])).

cnf(c_0_127,negated_conjecture,
    ( esk7_0 != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_118]),c_0_118])])).

cnf(c_0_128,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_125]),c_0_126])]),c_0_127]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:26:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.45  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.19/0.45  # and selection function SelectNegativeLiterals.
% 0.19/0.45  #
% 0.19/0.45  # Preprocessing time       : 0.027 s
% 0.19/0.45  # Presaturation interreduction done
% 0.19/0.45  
% 0.19/0.45  # Proof found!
% 0.19/0.45  # SZS status Theorem
% 0.19/0.45  # SZS output start CNFRefutation
% 0.19/0.45  fof(t43_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 0.19/0.45  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.45  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.45  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.45  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.45  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.45  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.19/0.45  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.45  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.45  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.45  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.45  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.45  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.45  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.19/0.45  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.45  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0))))), inference(assume_negation,[status(cth)],[t43_zfmisc_1])).
% 0.19/0.45  fof(c_0_16, plain, ![X43, X44]:k3_tarski(k2_tarski(X43,X44))=k2_xboole_0(X43,X44), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.45  fof(c_0_17, plain, ![X34, X35]:k1_enumset1(X34,X34,X35)=k2_tarski(X34,X35), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.45  fof(c_0_18, negated_conjecture, (((k1_tarski(esk5_0)=k2_xboole_0(esk6_0,esk7_0)&(esk6_0!=k1_tarski(esk5_0)|esk7_0!=k1_tarski(esk5_0)))&(esk6_0!=k1_xboole_0|esk7_0!=k1_tarski(esk5_0)))&(esk6_0!=k1_tarski(esk5_0)|esk7_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.19/0.45  fof(c_0_19, plain, ![X33]:k2_tarski(X33,X33)=k1_tarski(X33), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.45  cnf(c_0_20, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.45  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.45  fof(c_0_22, plain, ![X36, X37, X38]:k2_enumset1(X36,X36,X37,X38)=k1_enumset1(X36,X37,X38), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.45  fof(c_0_23, plain, ![X39, X40, X41, X42]:k3_enumset1(X39,X39,X40,X41,X42)=k2_enumset1(X39,X40,X41,X42), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.45  fof(c_0_24, plain, ![X19, X20, X21]:(~r1_tarski(X19,X20)|r1_tarski(X19,k2_xboole_0(X21,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.19/0.45  fof(c_0_25, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.45  fof(c_0_26, plain, ![X22, X23]:(~r1_tarski(X22,X23)|k2_xboole_0(X22,X23)=X23), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.45  cnf(c_0_27, negated_conjecture, (k1_tarski(esk5_0)=k2_xboole_0(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.45  cnf(c_0_28, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.45  cnf(c_0_29, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.45  cnf(c_0_30, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.45  cnf(c_0_31, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.45  fof(c_0_32, plain, ![X15]:(X15=k1_xboole_0|r2_hidden(esk3_1(X15),X15)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.45  cnf(c_0_33, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.45  cnf(c_0_34, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.45  cnf(c_0_35, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.45  cnf(c_0_36, negated_conjecture, (k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_21]), c_0_29]), c_0_30]), c_0_30]), c_0_31]), c_0_31])).
% 0.19/0.45  cnf(c_0_37, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.45  cnf(c_0_38, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_29]), c_0_30]), c_0_31])).
% 0.19/0.45  cnf(c_0_39, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_34])).
% 0.19/0.45  cnf(c_0_40, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_29]), c_0_30]), c_0_31])).
% 0.19/0.45  cnf(c_0_41, negated_conjecture, (k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,k1_xboole_0))=k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)|r2_hidden(esk3_1(esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.45  fof(c_0_42, plain, ![X26, X27, X28, X29, X30, X31]:(((~r2_hidden(X28,X27)|X28=X26|X27!=k1_tarski(X26))&(X29!=X26|r2_hidden(X29,X27)|X27!=k1_tarski(X26)))&((~r2_hidden(esk4_2(X30,X31),X31)|esk4_2(X30,X31)!=X30|X31=k1_tarski(X30))&(r2_hidden(esk4_2(X30,X31),X31)|esk4_2(X30,X31)=X30|X31=k1_tarski(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.45  fof(c_0_43, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.45  cnf(c_0_44, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.45  cnf(c_0_45, negated_conjecture, (esk6_0!=k1_tarski(esk5_0)|esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.45  cnf(c_0_46, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X1))=X1), inference(spm,[status(thm)],[c_0_40, c_0_39])).
% 0.19/0.45  cnf(c_0_47, negated_conjecture, (k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,X1))=k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)|r2_hidden(esk3_1(esk7_0),esk7_0)|r2_hidden(esk3_1(X1),X1)), inference(spm,[status(thm)],[c_0_41, c_0_37])).
% 0.19/0.45  fof(c_0_48, plain, ![X24, X25]:r1_tarski(X24,k2_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.45  cnf(c_0_49, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.45  cnf(c_0_50, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.45  cnf(c_0_51, negated_conjecture, (r1_tarski(esk7_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_44, c_0_36])).
% 0.19/0.45  cnf(c_0_52, negated_conjecture, (esk7_0!=k1_xboole_0|esk6_0!=k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_28]), c_0_21]), c_0_30]), c_0_31])).
% 0.19/0.45  cnf(c_0_53, negated_conjecture, (k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=esk6_0|r2_hidden(esk3_1(esk6_0),esk6_0)|r2_hidden(esk3_1(esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.45  cnf(c_0_54, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.45  cnf(c_0_55, plain, (X1=X3|X2!=k3_enumset1(X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_28]), c_0_21]), c_0_30]), c_0_31])).
% 0.19/0.45  cnf(c_0_56, negated_conjecture, (r2_hidden(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.45  cnf(c_0_57, negated_conjecture, (r2_hidden(esk3_1(esk7_0),esk7_0)|r2_hidden(esk3_1(esk6_0),esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_37])).
% 0.19/0.45  cnf(c_0_58, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_29]), c_0_30]), c_0_31])).
% 0.19/0.45  cnf(c_0_59, plain, (X1=X2|~r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_55])).
% 0.19/0.45  cnf(c_0_60, negated_conjecture, (r2_hidden(esk3_1(esk7_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|r2_hidden(esk3_1(esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.45  cnf(c_0_61, negated_conjecture, (r1_tarski(esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_58, c_0_36])).
% 0.19/0.45  cnf(c_0_62, negated_conjecture, (esk3_1(esk7_0)=esk5_0|r2_hidden(esk3_1(esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.19/0.45  cnf(c_0_63, negated_conjecture, (r2_hidden(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_50, c_0_61])).
% 0.19/0.45  cnf(c_0_64, negated_conjecture, (r2_hidden(esk3_1(esk6_0),esk6_0)|r2_hidden(esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_57, c_0_62])).
% 0.19/0.45  fof(c_0_65, plain, ![X45, X46, X47]:(((r2_hidden(X45,X47)|~r1_tarski(k2_tarski(X45,X46),X47))&(r2_hidden(X46,X47)|~r1_tarski(k2_tarski(X45,X46),X47)))&(~r2_hidden(X45,X47)|~r2_hidden(X46,X47)|r1_tarski(k2_tarski(X45,X46),X47))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.19/0.45  cnf(c_0_66, negated_conjecture, (r2_hidden(esk3_1(esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|r2_hidden(esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.19/0.45  cnf(c_0_67, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.19/0.45  cnf(c_0_68, negated_conjecture, (esk3_1(esk6_0)=esk5_0|r2_hidden(esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_59, c_0_66])).
% 0.19/0.45  cnf(c_0_69, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_21]), c_0_30]), c_0_31])).
% 0.19/0.45  cnf(c_0_70, negated_conjecture, (r2_hidden(esk5_0,esk7_0)|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_64, c_0_68])).
% 0.19/0.45  cnf(c_0_71, negated_conjecture, (r1_tarski(k3_enumset1(X1,X1,X1,X1,esk5_0),esk7_0)|r2_hidden(esk5_0,esk6_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.45  cnf(c_0_72, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.45  cnf(c_0_73, negated_conjecture, (r1_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk7_0)|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_71, c_0_70])).
% 0.19/0.45  cnf(c_0_74, negated_conjecture, (esk6_0!=k1_xboole_0|esk7_0!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.45  cnf(c_0_75, negated_conjecture, (k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=esk7_0|r2_hidden(esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_51])])).
% 0.19/0.45  cnf(c_0_76, negated_conjecture, (esk6_0!=k1_xboole_0|esk7_0!=k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_28]), c_0_21]), c_0_30]), c_0_31])).
% 0.19/0.45  cnf(c_0_77, negated_conjecture, (r1_tarski(esk6_0,esk7_0)|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_61, c_0_75])).
% 0.19/0.45  cnf(c_0_78, negated_conjecture, (r2_hidden(esk5_0,esk6_0)|esk6_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_76, c_0_75])).
% 0.19/0.45  cnf(c_0_79, negated_conjecture, (r2_hidden(esk5_0,esk6_0)|r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_50, c_0_77])).
% 0.19/0.45  cnf(c_0_80, negated_conjecture, (r2_hidden(esk3_1(esk6_0),esk6_0)|r2_hidden(esk5_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_78, c_0_37])).
% 0.19/0.45  cnf(c_0_81, negated_conjecture, (X1=esk5_0|r2_hidden(esk5_0,esk6_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_59, c_0_75])).
% 0.19/0.45  cnf(c_0_82, negated_conjecture, (r2_hidden(esk3_1(esk6_0),esk7_0)|r2_hidden(esk5_0,k1_xboole_0)|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.19/0.45  cnf(c_0_83, negated_conjecture, (esk3_1(esk6_0)=esk5_0|r2_hidden(esk5_0,k1_xboole_0)|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.19/0.45  cnf(c_0_84, negated_conjecture, (r2_hidden(esk5_0,k1_xboole_0)|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_80, c_0_83])).
% 0.19/0.45  cnf(c_0_85, negated_conjecture, (r1_tarski(k3_enumset1(X1,X1,X1,X1,esk5_0),esk6_0)|r2_hidden(esk5_0,k1_xboole_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_69, c_0_84])).
% 0.19/0.45  cnf(c_0_86, negated_conjecture, (r1_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)|r2_hidden(esk5_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_85, c_0_84])).
% 0.19/0.45  cnf(c_0_87, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.45  cnf(c_0_88, negated_conjecture, (esk6_0!=k1_tarski(esk5_0)|esk7_0!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.45  cnf(c_0_89, negated_conjecture, (k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=esk6_0|r2_hidden(esk5_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_86]), c_0_61])])).
% 0.19/0.45  cnf(c_0_90, plain, (X1=X2|r2_hidden(esk2_2(X1,X2),X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_72, c_0_87])).
% 0.19/0.45  cnf(c_0_91, negated_conjecture, (esk6_0!=k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)|esk7_0!=k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_28]), c_0_28]), c_0_21]), c_0_21]), c_0_30]), c_0_30]), c_0_31]), c_0_31])).
% 0.19/0.45  cnf(c_0_92, negated_conjecture, (r1_tarski(esk7_0,esk6_0)|r2_hidden(esk5_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_51, c_0_89])).
% 0.19/0.45  cnf(c_0_93, negated_conjecture, (r2_hidden(esk5_0,k1_xboole_0)|esk7_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_89])).
% 0.19/0.45  cnf(c_0_94, negated_conjecture, (k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=esk7_0|r2_hidden(esk2_2(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk7_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_90, c_0_51])).
% 0.19/0.45  cnf(c_0_95, negated_conjecture, (r2_hidden(esk5_0,k1_xboole_0)|esk7_0!=esk6_0), inference(spm,[status(thm)],[c_0_91, c_0_89])).
% 0.19/0.45  cnf(c_0_96, negated_conjecture, (r2_hidden(esk5_0,k1_xboole_0)|r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_50, c_0_92])).
% 0.19/0.45  cnf(c_0_97, negated_conjecture, (r2_hidden(esk3_1(esk7_0),esk7_0)|r2_hidden(esk5_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_93, c_0_37])).
% 0.19/0.45  cnf(c_0_98, negated_conjecture, (X1=esk5_0|r2_hidden(esk5_0,k1_xboole_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_59, c_0_89])).
% 0.19/0.45  cnf(c_0_99, negated_conjecture, (r2_hidden(esk2_2(esk6_0,esk7_0),esk6_0)|r2_hidden(esk5_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_89]), c_0_95])).
% 0.19/0.45  cnf(c_0_100, negated_conjecture, (r2_hidden(esk3_1(esk7_0),esk6_0)|r2_hidden(esk5_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.19/0.45  cnf(c_0_101, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.45  cnf(c_0_102, negated_conjecture, (esk2_2(esk6_0,esk7_0)=esk5_0|r2_hidden(esk5_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 0.19/0.45  cnf(c_0_103, negated_conjecture, (r2_hidden(esk5_0,k1_xboole_0)|~r1_tarski(esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_92]), c_0_95])).
% 0.19/0.45  fof(c_0_104, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.45  cnf(c_0_105, negated_conjecture, (esk3_1(esk7_0)=esk5_0|r2_hidden(esk5_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_98, c_0_100])).
% 0.19/0.45  cnf(c_0_106, negated_conjecture, (r2_hidden(esk5_0,k1_xboole_0)|~r2_hidden(esk5_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_103])).
% 0.19/0.45  cnf(c_0_107, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_104])).
% 0.19/0.45  cnf(c_0_108, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_104])).
% 0.19/0.45  cnf(c_0_109, negated_conjecture, (r2_hidden(esk5_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_105]), c_0_106])).
% 0.19/0.45  cnf(c_0_110, plain, (r2_hidden(esk1_1(X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_107, c_0_108])).
% 0.19/0.45  cnf(c_0_111, negated_conjecture, (r2_hidden(esk3_1(X1),X1)|r2_hidden(esk5_0,X1)), inference(spm,[status(thm)],[c_0_109, c_0_37])).
% 0.19/0.45  cnf(c_0_112, negated_conjecture, (r2_hidden(esk1_1(X1),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_110])).
% 0.19/0.45  cnf(c_0_113, negated_conjecture, (r2_hidden(esk1_1(esk7_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_56, c_0_112])).
% 0.19/0.45  cnf(c_0_114, negated_conjecture, (esk1_1(esk7_0)=esk5_0), inference(spm,[status(thm)],[c_0_59, c_0_113])).
% 0.19/0.45  cnf(c_0_115, negated_conjecture, (r2_hidden(esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_112, c_0_114])).
% 0.19/0.45  cnf(c_0_116, negated_conjecture, (r1_tarski(k3_enumset1(X1,X1,X1,X1,esk5_0),esk7_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_69, c_0_115])).
% 0.19/0.45  cnf(c_0_117, negated_conjecture, (r1_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk7_0)), inference(spm,[status(thm)],[c_0_116, c_0_115])).
% 0.19/0.45  cnf(c_0_118, negated_conjecture, (k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_117]), c_0_51])])).
% 0.19/0.45  cnf(c_0_119, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk6_0)), inference(rw,[status(thm)],[c_0_63, c_0_118])).
% 0.19/0.45  cnf(c_0_120, negated_conjecture, (X1=esk5_0|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_59, c_0_118])).
% 0.19/0.45  cnf(c_0_121, negated_conjecture, (r2_hidden(esk1_1(esk6_0),esk7_0)), inference(spm,[status(thm)],[c_0_119, c_0_112])).
% 0.19/0.45  cnf(c_0_122, negated_conjecture, (esk1_1(esk6_0)=esk5_0), inference(spm,[status(thm)],[c_0_120, c_0_121])).
% 0.19/0.45  cnf(c_0_123, negated_conjecture, (r1_tarski(k3_enumset1(X1,X1,X1,X1,esk1_1(X2)),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_69, c_0_112])).
% 0.19/0.45  cnf(c_0_124, negated_conjecture, (r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_112, c_0_122])).
% 0.19/0.45  cnf(c_0_125, negated_conjecture, (r1_tarski(esk7_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_124]), c_0_122]), c_0_118])).
% 0.19/0.45  cnf(c_0_126, negated_conjecture, (r1_tarski(esk6_0,esk7_0)), inference(rw,[status(thm)],[c_0_61, c_0_118])).
% 0.19/0.45  cnf(c_0_127, negated_conjecture, (esk7_0!=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_118]), c_0_118])])).
% 0.19/0.45  cnf(c_0_128, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_125]), c_0_126])]), c_0_127]), ['proof']).
% 0.19/0.45  # SZS output end CNFRefutation
% 0.19/0.45  # Proof object total steps             : 129
% 0.19/0.45  # Proof object clause steps            : 98
% 0.19/0.45  # Proof object formula steps           : 31
% 0.19/0.45  # Proof object conjectures             : 71
% 0.19/0.45  # Proof object clause conjectures      : 68
% 0.19/0.45  # Proof object formula conjectures     : 3
% 0.19/0.45  # Proof object initial clauses used    : 22
% 0.19/0.45  # Proof object initial formulas used   : 15
% 0.19/0.45  # Proof object generating inferences   : 61
% 0.19/0.45  # Proof object simplifying inferences  : 64
% 0.19/0.45  # Training examples: 0 positive, 0 negative
% 0.19/0.45  # Parsed axioms                        : 15
% 0.19/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.45  # Initial clauses                      : 28
% 0.19/0.45  # Removed in clause preprocessing      : 5
% 0.19/0.45  # Initial clauses in saturation        : 23
% 0.19/0.45  # Processed clauses                    : 628
% 0.19/0.45  # ...of these trivial                  : 7
% 0.19/0.45  # ...subsumed                          : 296
% 0.19/0.45  # ...remaining for further processing  : 325
% 0.19/0.45  # Other redundant clauses eliminated   : 180
% 0.19/0.45  # Clauses deleted for lack of memory   : 0
% 0.19/0.45  # Backward-subsumed                    : 35
% 0.19/0.45  # Backward-rewritten                   : 139
% 0.19/0.45  # Generated clauses                    : 4867
% 0.19/0.45  # ...of the previous two non-trivial   : 4471
% 0.19/0.45  # Contextual simplify-reflections      : 9
% 0.19/0.45  # Paramodulations                      : 4687
% 0.19/0.45  # Factorizations                       : 1
% 0.19/0.45  # Equation resolutions                 : 180
% 0.19/0.45  # Propositional unsat checks           : 0
% 0.19/0.45  #    Propositional check models        : 0
% 0.19/0.45  #    Propositional check unsatisfiable : 0
% 0.19/0.45  #    Propositional clauses             : 0
% 0.19/0.45  #    Propositional clauses after purity: 0
% 0.19/0.45  #    Propositional unsat core size     : 0
% 0.19/0.45  #    Propositional preprocessing time  : 0.000
% 0.19/0.45  #    Propositional encoding time       : 0.000
% 0.19/0.45  #    Propositional solver time         : 0.000
% 0.19/0.45  #    Success case prop preproc time    : 0.000
% 0.19/0.45  #    Success case prop encoding time   : 0.000
% 0.19/0.45  #    Success case prop solver time     : 0.000
% 0.19/0.45  # Current number of processed clauses  : 125
% 0.19/0.45  #    Positive orientable unit clauses  : 25
% 0.19/0.45  #    Positive unorientable unit clauses: 0
% 0.19/0.45  #    Negative unit clauses             : 2
% 0.19/0.45  #    Non-unit-clauses                  : 98
% 0.19/0.45  # Current number of unprocessed clauses: 3852
% 0.19/0.45  # ...number of literals in the above   : 13353
% 0.19/0.45  # Current number of archived formulas  : 0
% 0.19/0.45  # Current number of archived clauses   : 201
% 0.19/0.45  # Clause-clause subsumption calls (NU) : 5636
% 0.19/0.45  # Rec. Clause-clause subsumption calls : 3500
% 0.19/0.45  # Non-unit clause-clause subsumptions  : 317
% 0.19/0.45  # Unit Clause-clause subsumption calls : 1156
% 0.19/0.45  # Rewrite failures with RHS unbound    : 0
% 0.19/0.45  # BW rewrite match attempts            : 76
% 0.19/0.45  # BW rewrite match successes           : 18
% 0.19/0.45  # Condensation attempts                : 0
% 0.19/0.45  # Condensation successes               : 0
% 0.19/0.45  # Termbank termtop insertions          : 71057
% 0.19/0.46  
% 0.19/0.46  # -------------------------------------------------
% 0.19/0.46  # User time                : 0.102 s
% 0.19/0.46  # System time              : 0.007 s
% 0.19/0.46  # Total time               : 0.109 s
% 0.19/0.46  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
