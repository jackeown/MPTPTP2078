%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:06 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 863 expanded)
%              Number of clauses        :   47 ( 354 expanded)
%              Number of leaves         :   19 ( 248 expanded)
%              Depth                    :   11
%              Number of atoms          :  186 (1237 expanded)
%              Number of equality atoms :   51 ( 775 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t13_ordinal1,conjecture,(
    ! [X1,X2] :
      ( r2_hidden(X1,k1_ordinal1(X2))
    <=> ( r2_hidden(X1,X2)
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t144_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3)
        & X3 != k4_xboole_0(X3,k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ~ ( r1_xboole_0(X1,X2)
        & r2_hidden(X3,k2_xboole_0(X1,X2))
        & ~ ( r2_hidden(X3,X1)
            & ~ r2_hidden(X3,X2) )
        & ~ ( r2_hidden(X3,X2)
            & ~ r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_xboole_0)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(t8_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(k1_setfam_1(X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).

fof(t11_setfam_1,axiom,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r2_hidden(X1,k1_ordinal1(X2))
      <=> ( r2_hidden(X1,X2)
          | X1 = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t13_ordinal1])).

fof(c_0_20,plain,(
    ! [X42] : k1_ordinal1(X42) = k2_xboole_0(X42,k1_tarski(X42)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_21,plain,(
    ! [X21] : k2_tarski(X21,X21) = k1_tarski(X21) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_22,plain,(
    ! [X33,X34] : k3_tarski(k2_tarski(X33,X34)) = k2_xboole_0(X33,X34) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_23,plain,(
    ! [X22,X23] : k1_enumset1(X22,X22,X23) = k2_tarski(X22,X23) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_24,negated_conjecture,
    ( ( ~ r2_hidden(esk2_0,esk3_0)
      | ~ r2_hidden(esk2_0,k1_ordinal1(esk3_0)) )
    & ( esk2_0 != esk3_0
      | ~ r2_hidden(esk2_0,k1_ordinal1(esk3_0)) )
    & ( r2_hidden(esk2_0,k1_ordinal1(esk3_0))
      | r2_hidden(esk2_0,esk3_0)
      | esk2_0 = esk3_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])])).

cnf(c_0_25,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X24,X25,X26] : k2_enumset1(X24,X24,X25,X26) = k1_enumset1(X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_30,plain,(
    ! [X27,X28,X29,X30] : k3_enumset1(X27,X27,X28,X29,X30) = k2_enumset1(X27,X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_31,plain,(
    ! [X17,X18] : r1_tarski(X17,k2_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_32,plain,(
    ! [X35,X36,X37] :
      ( r2_hidden(X35,X37)
      | r2_hidden(X36,X37)
      | X37 = k4_xboole_0(X37,k2_tarski(X35,X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t144_zfmisc_1])])])).

cnf(c_0_33,negated_conjecture,
    ( esk2_0 != esk3_0
    | ~ r2_hidden(esk2_0,k1_ordinal1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk2_0,k1_ordinal1(esk3_0))
    | r2_hidden(esk2_0,esk3_0)
    | esk2_0 = esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_39,plain,(
    ! [X43] : r2_hidden(X43,k1_ordinal1(X43)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

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

cnf(c_0_41,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_42,plain,(
    ! [X12,X13,X14] :
      ( ( r2_hidden(X14,X13)
        | r2_hidden(X14,X12)
        | ~ r1_xboole_0(X12,X13)
        | ~ r2_hidden(X14,k2_xboole_0(X12,X13)) )
      & ( ~ r2_hidden(X14,X12)
        | r2_hidden(X14,X12)
        | ~ r1_xboole_0(X12,X13)
        | ~ r2_hidden(X14,k2_xboole_0(X12,X13)) )
      & ( r2_hidden(X14,X13)
        | ~ r2_hidden(X14,X13)
        | ~ r1_xboole_0(X12,X13)
        | ~ r2_hidden(X14,k2_xboole_0(X12,X13)) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | ~ r1_xboole_0(X12,X13)
        | ~ r2_hidden(X14,k2_xboole_0(X12,X13)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_xboole_0])])])])).

fof(c_0_43,plain,(
    ! [X19,X20] :
      ( ( ~ r1_xboole_0(X19,X20)
        | k4_xboole_0(X19,X20) = X19 )
      & ( k4_xboole_0(X19,X20) != X19
        | r1_xboole_0(X19,X20) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | X2 = k4_xboole_0(X2,k2_tarski(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_45,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(X15,X16)
        | X15 != X16 )
      & ( r1_tarski(X16,X15)
        | X15 != X16 )
      & ( ~ r1_tarski(X15,X16)
        | ~ r1_tarski(X16,X15)
        | X15 = X16 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_46,negated_conjecture,
    ( esk3_0 != esk2_0
    | ~ r2_hidden(esk2_0,k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_28]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( esk3_0 = esk2_0
    | r2_hidden(esk2_0,esk3_0)
    | r2_hidden(esk2_0,k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_34]),c_0_28]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r1_xboole_0(X3,X2)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( X2 = k4_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X3))
    | r2_hidden(X3,X2)
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_28]),c_0_36]),c_0_37])).

fof(c_0_54,plain,(
    ! [X44,X45] :
      ( ~ r2_hidden(X44,X45)
      | ~ r1_tarski(X45,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0)
    | ~ r2_hidden(esk2_0,k1_ordinal1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk2_0,k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))
    | r2_hidden(esk2_0,esk3_0)
    | ~ r2_hidden(esk3_0,k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,k3_enumset1(X1,X1,X1,X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_34]),c_0_28]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X2)
    | ~ r1_xboole_0(X3,X2)
    | ~ r2_hidden(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_61,plain,
    ( r1_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X3))
    | r2_hidden(X2,X1)
    | r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0)
    | ~ r2_hidden(esk2_0,k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_34]),c_0_28]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk2_0,k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58])]),c_0_59])).

fof(c_0_66,plain,(
    ! [X11] : k2_xboole_0(X11,X11) = X11 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_67,plain,(
    ! [X31,X32] :
      ( ~ r2_hidden(X31,X32)
      | r1_tarski(X31,k3_tarski(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X3))
    | r2_hidden(X3,X4)
    | r2_hidden(X2,X4)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,k3_tarski(k3_enumset1(X4,X4,X4,X4,k3_enumset1(X2,X2,X2,X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_69,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65])])).

cnf(c_0_71,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

fof(c_0_72,plain,(
    ! [X39,X40,X41] :
      ( ~ r2_hidden(X39,X40)
      | ~ r1_tarski(X39,X41)
      | r1_tarski(k1_setfam_1(X40),X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_setfam_1])])).

fof(c_0_73,plain,(
    ! [X38] : k1_setfam_1(k1_tarski(X38)) = X38 ),
    inference(variable_rename,[status(thm)],[t11_setfam_1])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk2_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_65]),c_0_69]),c_0_70])).

cnf(c_0_76,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_77,plain,
    ( r1_tarski(k1_setfam_1(X2),X3)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_78,plain,
    ( k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_79,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_65])])).

cnf(c_0_82,plain,
    ( r1_tarski(k1_setfam_1(X1),X2)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_63])).

cnf(c_0_83,plain,
    ( k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_26]),c_0_28]),c_0_36]),c_0_37])).

cnf(c_0_84,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_75]),c_0_83]),c_0_84]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.08/0.28  % Computer   : n023.cluster.edu
% 0.08/0.28  % Model      : x86_64 x86_64
% 0.08/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.28  % Memory     : 8042.1875MB
% 0.08/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.28  % CPULimit   : 60
% 0.08/0.28  % WCLimit    : 600
% 0.08/0.28  % DateTime   : Tue Dec  1 13:49:20 EST 2020
% 0.08/0.28  % CPUTime    : 
% 0.08/0.28  # Version: 2.5pre002
% 0.08/0.28  # No SInE strategy applied
% 0.08/0.28  # Trying AutoSched0 for 299 seconds
% 3.84/4.08  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 3.84/4.08  # and selection function SelectNegativeLiterals.
% 3.84/4.08  #
% 3.84/4.08  # Preprocessing time       : 0.013 s
% 3.84/4.08  # Presaturation interreduction done
% 3.84/4.08  
% 3.84/4.08  # Proof found!
% 3.84/4.08  # SZS status Theorem
% 3.84/4.08  # SZS output start CNFRefutation
% 3.84/4.08  fof(t13_ordinal1, conjecture, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 3.84/4.08  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 3.84/4.08  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.84/4.08  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.84/4.08  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.84/4.08  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.84/4.08  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.84/4.08  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.84/4.08  fof(t144_zfmisc_1, axiom, ![X1, X2, X3]:~(((~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))&X3!=k4_xboole_0(X3,k2_tarski(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 3.84/4.08  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 3.84/4.08  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.84/4.08  fof(t5_xboole_0, axiom, ![X1, X2, X3]:~((((r1_xboole_0(X1,X2)&r2_hidden(X3,k2_xboole_0(X1,X2)))&~((r2_hidden(X3,X1)&~(r2_hidden(X3,X2)))))&~((r2_hidden(X3,X2)&~(r2_hidden(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_xboole_0)).
% 3.84/4.08  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.84/4.08  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.84/4.08  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.84/4.08  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.84/4.08  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 3.84/4.08  fof(t8_setfam_1, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(k1_setfam_1(X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_setfam_1)).
% 3.84/4.08  fof(t11_setfam_1, axiom, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 3.84/4.08  fof(c_0_19, negated_conjecture, ~(![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2))), inference(assume_negation,[status(cth)],[t13_ordinal1])).
% 3.84/4.08  fof(c_0_20, plain, ![X42]:k1_ordinal1(X42)=k2_xboole_0(X42,k1_tarski(X42)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 3.84/4.08  fof(c_0_21, plain, ![X21]:k2_tarski(X21,X21)=k1_tarski(X21), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 3.84/4.08  fof(c_0_22, plain, ![X33, X34]:k3_tarski(k2_tarski(X33,X34))=k2_xboole_0(X33,X34), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 3.84/4.08  fof(c_0_23, plain, ![X22, X23]:k1_enumset1(X22,X22,X23)=k2_tarski(X22,X23), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 3.84/4.08  fof(c_0_24, negated_conjecture, (((~r2_hidden(esk2_0,esk3_0)|~r2_hidden(esk2_0,k1_ordinal1(esk3_0)))&(esk2_0!=esk3_0|~r2_hidden(esk2_0,k1_ordinal1(esk3_0))))&(r2_hidden(esk2_0,k1_ordinal1(esk3_0))|(r2_hidden(esk2_0,esk3_0)|esk2_0=esk3_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])])).
% 3.84/4.08  cnf(c_0_25, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.84/4.08  cnf(c_0_26, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 3.84/4.08  cnf(c_0_27, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 3.84/4.08  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.84/4.08  fof(c_0_29, plain, ![X24, X25, X26]:k2_enumset1(X24,X24,X25,X26)=k1_enumset1(X24,X25,X26), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 3.84/4.08  fof(c_0_30, plain, ![X27, X28, X29, X30]:k3_enumset1(X27,X27,X28,X29,X30)=k2_enumset1(X27,X28,X29,X30), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 3.84/4.08  fof(c_0_31, plain, ![X17, X18]:r1_tarski(X17,k2_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 3.84/4.08  fof(c_0_32, plain, ![X35, X36, X37]:(r2_hidden(X35,X37)|r2_hidden(X36,X37)|X37=k4_xboole_0(X37,k2_tarski(X35,X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t144_zfmisc_1])])])).
% 3.84/4.08  cnf(c_0_33, negated_conjecture, (esk2_0!=esk3_0|~r2_hidden(esk2_0,k1_ordinal1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 3.84/4.08  cnf(c_0_34, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 3.84/4.08  cnf(c_0_35, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 3.84/4.08  cnf(c_0_36, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 3.84/4.08  cnf(c_0_37, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 3.84/4.08  cnf(c_0_38, negated_conjecture, (r2_hidden(esk2_0,k1_ordinal1(esk3_0))|r2_hidden(esk2_0,esk3_0)|esk2_0=esk3_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 3.84/4.08  fof(c_0_39, plain, ![X43]:r2_hidden(X43,k1_ordinal1(X43)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 3.84/4.08  fof(c_0_40, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 3.84/4.08  cnf(c_0_41, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.84/4.08  fof(c_0_42, plain, ![X12, X13, X14]:(((r2_hidden(X14,X13)|(r2_hidden(X14,X12)|(~r1_xboole_0(X12,X13)|~r2_hidden(X14,k2_xboole_0(X12,X13)))))&(~r2_hidden(X14,X12)|(r2_hidden(X14,X12)|(~r1_xboole_0(X12,X13)|~r2_hidden(X14,k2_xboole_0(X12,X13))))))&((r2_hidden(X14,X13)|(~r2_hidden(X14,X13)|(~r1_xboole_0(X12,X13)|~r2_hidden(X14,k2_xboole_0(X12,X13)))))&(~r2_hidden(X14,X12)|(~r2_hidden(X14,X13)|(~r1_xboole_0(X12,X13)|~r2_hidden(X14,k2_xboole_0(X12,X13))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_xboole_0])])])])).
% 3.84/4.08  fof(c_0_43, plain, ![X19, X20]:((~r1_xboole_0(X19,X20)|k4_xboole_0(X19,X20)=X19)&(k4_xboole_0(X19,X20)!=X19|r1_xboole_0(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 3.84/4.08  cnf(c_0_44, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|X2=k4_xboole_0(X2,k2_tarski(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 3.84/4.08  fof(c_0_45, plain, ![X15, X16]:(((r1_tarski(X15,X16)|X15!=X16)&(r1_tarski(X16,X15)|X15!=X16))&(~r1_tarski(X15,X16)|~r1_tarski(X16,X15)|X15=X16)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 3.84/4.08  cnf(c_0_46, negated_conjecture, (esk3_0!=esk2_0|~r2_hidden(esk2_0,k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_28]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 3.84/4.08  cnf(c_0_47, negated_conjecture, (esk3_0=esk2_0|r2_hidden(esk2_0,esk3_0)|r2_hidden(esk2_0,k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_34]), c_0_28]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 3.84/4.08  cnf(c_0_48, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 3.84/4.08  cnf(c_0_49, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 3.84/4.08  cnf(c_0_50, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_35]), c_0_36]), c_0_37])).
% 3.84/4.08  cnf(c_0_51, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r1_xboole_0(X3,X2)|~r2_hidden(X1,k2_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 3.84/4.08  cnf(c_0_52, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_43])).
% 3.84/4.08  cnf(c_0_53, plain, (X2=k4_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X3))|r2_hidden(X3,X2)|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_28]), c_0_36]), c_0_37])).
% 3.84/4.08  fof(c_0_54, plain, ![X44, X45]:(~r2_hidden(X44,X45)|~r1_tarski(X45,X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 3.84/4.08  cnf(c_0_55, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 3.84/4.08  cnf(c_0_56, negated_conjecture, (~r2_hidden(esk2_0,esk3_0)|~r2_hidden(esk2_0,k1_ordinal1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 3.84/4.08  cnf(c_0_57, negated_conjecture, (r2_hidden(esk2_0,k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))|r2_hidden(esk2_0,esk3_0)|~r2_hidden(esk3_0,k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 3.84/4.08  cnf(c_0_58, plain, (r2_hidden(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,k3_enumset1(X1,X1,X1,X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_34]), c_0_28]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 3.84/4.08  cnf(c_0_59, plain, (r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 3.84/4.08  cnf(c_0_60, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X2)|~r1_xboole_0(X3,X2)|~r2_hidden(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_35]), c_0_36]), c_0_37])).
% 3.84/4.08  cnf(c_0_61, plain, (r1_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X3))|r2_hidden(X2,X1)|r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 3.84/4.08  cnf(c_0_62, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 3.84/4.08  cnf(c_0_63, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_55])).
% 3.84/4.08  cnf(c_0_64, negated_conjecture, (~r2_hidden(esk2_0,esk3_0)|~r2_hidden(esk2_0,k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_34]), c_0_28]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 3.84/4.08  cnf(c_0_65, negated_conjecture, (r2_hidden(esk2_0,k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58])]), c_0_59])).
% 3.84/4.08  fof(c_0_66, plain, ![X11]:k2_xboole_0(X11,X11)=X11, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 3.84/4.08  fof(c_0_67, plain, ![X31, X32]:(~r2_hidden(X31,X32)|r1_tarski(X31,k3_tarski(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 3.84/4.08  cnf(c_0_68, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X3))|r2_hidden(X3,X4)|r2_hidden(X2,X4)|r2_hidden(X1,X4)|~r2_hidden(X1,k3_tarski(k3_enumset1(X4,X4,X4,X4,k3_enumset1(X2,X2,X2,X2,X3))))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 3.84/4.08  cnf(c_0_69, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 3.84/4.08  cnf(c_0_70, negated_conjecture, (~r2_hidden(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65])])).
% 3.84/4.08  cnf(c_0_71, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_66])).
% 3.84/4.08  fof(c_0_72, plain, ![X39, X40, X41]:(~r2_hidden(X39,X40)|~r1_tarski(X39,X41)|r1_tarski(k1_setfam_1(X40),X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_setfam_1])])).
% 3.84/4.08  fof(c_0_73, plain, ![X38]:k1_setfam_1(k1_tarski(X38))=X38, inference(variable_rename,[status(thm)],[t11_setfam_1])).
% 3.84/4.08  cnf(c_0_74, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 3.84/4.08  cnf(c_0_75, negated_conjecture, (r2_hidden(esk2_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_65]), c_0_69]), c_0_70])).
% 3.84/4.08  cnf(c_0_76, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_35]), c_0_36]), c_0_37])).
% 3.84/4.08  cnf(c_0_77, plain, (r1_tarski(k1_setfam_1(X2),X3)|~r2_hidden(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 3.84/4.08  cnf(c_0_78, plain, (k1_setfam_1(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_73])).
% 3.84/4.08  cnf(c_0_79, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 3.84/4.08  cnf(c_0_80, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])).
% 3.84/4.08  cnf(c_0_81, negated_conjecture, (esk2_0!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_65])])).
% 3.84/4.08  cnf(c_0_82, plain, (r1_tarski(k1_setfam_1(X1),X2)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_77, c_0_63])).
% 3.84/4.08  cnf(c_0_83, plain, (k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_26]), c_0_28]), c_0_36]), c_0_37])).
% 3.84/4.08  cnf(c_0_84, negated_conjecture, (~r1_tarski(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])).
% 3.84/4.08  cnf(c_0_85, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_75]), c_0_83]), c_0_84]), ['proof']).
% 3.84/4.08  # SZS output end CNFRefutation
% 3.84/4.08  # Proof object total steps             : 86
% 3.84/4.08  # Proof object clause steps            : 47
% 3.84/4.08  # Proof object formula steps           : 39
% 3.84/4.08  # Proof object conjectures             : 17
% 3.84/4.08  # Proof object clause conjectures      : 14
% 3.84/4.08  # Proof object formula conjectures     : 3
% 3.84/4.08  # Proof object initial clauses used    : 22
% 3.84/4.08  # Proof object initial formulas used   : 19
% 3.84/4.08  # Proof object generating inferences   : 10
% 3.84/4.08  # Proof object simplifying inferences  : 60
% 3.84/4.08  # Training examples: 0 positive, 0 negative
% 3.84/4.08  # Parsed axioms                        : 19
% 3.84/4.08  # Removed by relevancy pruning/SinE    : 0
% 3.84/4.08  # Initial clauses                      : 29
% 3.84/4.08  # Removed in clause preprocessing      : 8
% 3.84/4.08  # Initial clauses in saturation        : 21
% 3.84/4.08  # Processed clauses                    : 8900
% 3.84/4.08  # ...of these trivial                  : 1
% 3.84/4.08  # ...subsumed                          : 6197
% 3.84/4.08  # ...remaining for further processing  : 2701
% 3.84/4.08  # Other redundant clauses eliminated   : 21
% 3.84/4.08  # Clauses deleted for lack of memory   : 0
% 3.84/4.08  # Backward-subsumed                    : 64
% 3.84/4.08  # Backward-rewritten                   : 17
% 3.84/4.08  # Generated clauses                    : 314188
% 3.84/4.08  # ...of the previous two non-trivial   : 308205
% 3.84/4.08  # Contextual simplify-reflections      : 12
% 3.84/4.08  # Paramodulations                      : 314083
% 3.84/4.08  # Factorizations                       : 82
% 3.84/4.08  # Equation resolutions                 : 21
% 3.84/4.08  # Propositional unsat checks           : 0
% 3.84/4.08  #    Propositional check models        : 0
% 3.84/4.08  #    Propositional check unsatisfiable : 0
% 3.84/4.08  #    Propositional clauses             : 0
% 3.84/4.08  #    Propositional clauses after purity: 0
% 3.84/4.08  #    Propositional unsat core size     : 0
% 3.84/4.08  #    Propositional preprocessing time  : 0.000
% 3.84/4.08  #    Propositional encoding time       : 0.000
% 3.84/4.08  #    Propositional solver time         : 0.000
% 3.84/4.08  #    Success case prop preproc time    : 0.000
% 3.84/4.08  #    Success case prop encoding time   : 0.000
% 3.84/4.08  #    Success case prop solver time     : 0.000
% 3.84/4.08  # Current number of processed clauses  : 2596
% 3.84/4.08  #    Positive orientable unit clauses  : 39
% 3.84/4.08  #    Positive unorientable unit clauses: 0
% 3.84/4.08  #    Negative unit clauses             : 20
% 3.84/4.08  #    Non-unit-clauses                  : 2537
% 3.84/4.08  # Current number of unprocessed clauses: 299244
% 3.84/4.08  # ...number of literals in the above   : 1630641
% 3.84/4.08  # Current number of archived formulas  : 0
% 3.84/4.08  # Current number of archived clauses   : 109
% 3.84/4.08  # Clause-clause subsumption calls (NU) : 504094
% 3.84/4.08  # Rec. Clause-clause subsumption calls : 146735
% 3.84/4.08  # Non-unit clause-clause subsumptions  : 5851
% 3.84/4.08  # Unit Clause-clause subsumption calls : 1710
% 3.84/4.08  # Rewrite failures with RHS unbound    : 0
% 3.84/4.08  # BW rewrite match attempts            : 319
% 3.84/4.08  # BW rewrite match successes           : 3
% 3.84/4.08  # Condensation attempts                : 0
% 3.84/4.08  # Condensation successes               : 0
% 3.84/4.08  # Termbank termtop insertions          : 11795199
% 3.93/4.09  
% 3.93/4.09  # -------------------------------------------------
% 3.93/4.09  # User time                : 3.672 s
% 3.93/4.09  # System time              : 0.137 s
% 3.93/4.09  # Total time               : 3.809 s
% 3.93/4.09  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
