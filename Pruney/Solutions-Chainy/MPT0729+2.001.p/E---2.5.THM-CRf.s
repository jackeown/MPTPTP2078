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
% DateTime   : Thu Dec  3 10:56:04 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  116 (1210 expanded)
%              Number of clauses        :   71 ( 493 expanded)
%              Number of leaves         :   22 ( 355 expanded)
%              Depth                    :   16
%              Number of atoms          :  211 (1402 expanded)
%              Number of equality atoms :   90 (1163 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t12_ordinal1,conjecture,(
    ! [X1,X2] :
      ( k1_ordinal1(X1) = k1_ordinal1(X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_ordinal1)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_22,plain,(
    ! [X61] : k1_ordinal1(X61) = k2_xboole_0(X61,k1_tarski(X61)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_23,plain,(
    ! [X43] : k2_tarski(X43,X43) = k1_tarski(X43) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_24,plain,(
    ! [X55,X56] : k3_tarski(k2_tarski(X55,X56)) = k2_xboole_0(X55,X56) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_25,plain,(
    ! [X44,X45] : k1_enumset1(X44,X44,X45) = k2_tarski(X44,X45) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k1_ordinal1(X1) = k1_ordinal1(X2)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t12_ordinal1])).

fof(c_0_27,plain,(
    ! [X62] : r2_hidden(X62,k1_ordinal1(X62)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

cnf(c_0_28,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
    ! [X46,X47,X48] : k2_enumset1(X46,X46,X47,X48) = k1_enumset1(X46,X47,X48) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_33,plain,(
    ! [X49,X50,X51,X52] : k3_enumset1(X49,X49,X50,X51,X52) = k2_enumset1(X49,X50,X51,X52) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_34,negated_conjecture,
    ( k1_ordinal1(esk3_0) = k1_ordinal1(esk4_0)
    & esk3_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

fof(c_0_35,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(X23,k2_xboole_0(X24,X25))
      | r1_tarski(k4_xboole_0(X23,X24),X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

fof(c_0_36,plain,(
    ! [X34,X35] : k2_tarski(X34,X35) = k2_tarski(X35,X34) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_37,plain,(
    ! [X53,X54] :
      ( ( ~ r1_tarski(k1_tarski(X53),X54)
        | r2_hidden(X53,X54) )
      & ( ~ r2_hidden(X53,X54)
        | r1_tarski(k1_tarski(X53),X54) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_40,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( k1_ordinal1(esk3_0) = k1_ordinal1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,k3_enumset1(X1,X1,X1,X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_31]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) = k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_39]),c_0_39]),c_0_31]),c_0_31]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_42])).

fof(c_0_49,plain,(
    ! [X59,X60] : k1_setfam_1(k2_tarski(X59,X60)) = k3_xboole_0(X59,X60) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

cnf(c_0_50,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_51,plain,
    ( k3_enumset1(X1,X1,X1,X1,X2) = k3_enumset1(X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_31]),c_0_31]),c_0_41]),c_0_41]),c_0_42]),c_0_42])).

cnf(c_0_52,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_29]),c_0_31]),c_0_41]),c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk3_0,k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_54,plain,(
    ! [X57,X58] :
      ( ( k4_xboole_0(X57,k1_tarski(X58)) != X57
        | ~ r2_hidden(X58,X57) )
      & ( r2_hidden(X58,X57)
        | k4_xboole_0(X57,k1_tarski(X58)) = X57 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_55,plain,(
    ! [X30,X31] : r1_tarski(X30,k2_xboole_0(X30,X31)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_56,plain,(
    ! [X28,X29] : k2_xboole_0(k3_xboole_0(X28,X29),k4_xboole_0(X28,X29)) = X28 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_57,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_58,plain,(
    ! [X26,X27] : k4_xboole_0(X26,k4_xboole_0(X26,X27)) = k3_xboole_0(X26,X27) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_59,plain,(
    ! [X36,X37,X38,X39,X40,X41] :
      ( ( ~ r2_hidden(X38,X37)
        | X38 = X36
        | X37 != k1_tarski(X36) )
      & ( X39 != X36
        | r2_hidden(X39,X37)
        | X37 != k1_tarski(X36) )
      & ( ~ r2_hidden(esk2_2(X40,X41),X41)
        | esk2_2(X40,X41) != X40
        | X41 = k1_tarski(X40) )
      & ( r2_hidden(esk2_2(X40,X41),X41)
        | esk2_2(X40,X41) = X40
        | X41 = k1_tarski(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_60,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(X2,k1_tarski(X1)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_63,plain,(
    ! [X63,X64] :
      ( ~ r2_hidden(X63,X64)
      | ~ r1_tarski(X64,X63) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_66,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_57,c_0_31])).

cnf(c_0_67,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_68,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_71,plain,
    ( k4_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1)) = X2
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_29]),c_0_31]),c_0_41]),c_0_42])).

cnf(c_0_72,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_74,plain,
    ( k3_tarski(k3_enumset1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_40]),c_0_66]),c_0_66]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_42])).

cnf(c_0_75,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_66]),c_0_41]),c_0_42])).

fof(c_0_76,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k4_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_77,plain,
    ( X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_29]),c_0_31]),c_0_41]),c_0_42])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_29]),c_0_31]),c_0_41]),c_0_42])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)
    | r2_hidden(esk4_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_80,plain,
    ( ~ r2_hidden(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_81,plain,
    ( k3_tarski(k3_enumset1(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75]),c_0_75]),c_0_75]),c_0_75]),c_0_51])).

cnf(c_0_82,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_83,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk4_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))
    | r2_hidden(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_85,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_86,plain,(
    ! [X21,X22] :
      ( ~ r1_tarski(X21,X22)
      | k3_xboole_0(X21,X22) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(esk3_0,k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_48])).

cnf(c_0_88,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_89,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_51]),c_0_75])).

cnf(c_0_90,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_82])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85])).

cnf(c_0_92,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_87])).

cnf(c_0_94,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk3_0,k4_xboole_0(esk4_0,X1))
    | r2_hidden(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_96,plain,
    ( k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_66]),c_0_41]),c_0_42])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | r2_hidden(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_71])).

fof(c_0_98,plain,(
    ! [X5,X6] :
      ( ~ r2_hidden(X5,X6)
      | ~ r2_hidden(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

fof(c_0_99,plain,(
    ! [X19,X20] :
      ( ( r1_tarski(X19,X20)
        | X19 != X20 )
      & ( r1_tarski(X20,X19)
        | X19 != X20 )
      & ( ~ r1_tarski(X19,X20)
        | ~ r1_tarski(X20,X19)
        | X19 = X20 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_100,negated_conjecture,
    ( r2_hidden(esk3_0,k4_xboole_0(esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,esk3_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))
    | ~ r1_tarski(X1,k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_48])).

cnf(c_0_102,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)) = esk3_0
    | r2_hidden(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_51]),c_0_75])).

cnf(c_0_103,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_104,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_105,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k4_xboole_0(esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_100])).

cnf(c_0_106,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk4_0,esk3_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_73])).

cnf(c_0_107,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k4_xboole_0(esk4_0,esk3_0))) = esk4_0
    | r2_hidden(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_102])).

cnf(c_0_108,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_91])).

cnf(c_0_109,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_110,negated_conjecture,
    ( k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k4_xboole_0(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_106])])).

cnf(c_0_111,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k4_xboole_0(esk4_0,esk3_0))) = esk4_0 ),
    inference(sr,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_112,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_109])).

cnf(c_0_113,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_110]),c_0_111])).

cnf(c_0_114,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_112])).

cnf(c_0_115,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_113]),c_0_114]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:54:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.41  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.13/0.41  # and selection function SelectNegativeLiterals.
% 0.13/0.41  #
% 0.13/0.41  # Preprocessing time       : 0.028 s
% 0.13/0.41  # Presaturation interreduction done
% 0.13/0.41  
% 0.13/0.41  # Proof found!
% 0.13/0.41  # SZS status Theorem
% 0.13/0.41  # SZS output start CNFRefutation
% 0.13/0.41  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.13/0.41  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.41  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.13/0.41  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.41  fof(t12_ordinal1, conjecture, ![X1, X2]:(k1_ordinal1(X1)=k1_ordinal1(X2)=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_ordinal1)).
% 0.13/0.41  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 0.13/0.41  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.41  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.41  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.13/0.41  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.13/0.41  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.13/0.41  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.13/0.41  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.13/0.41  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.13/0.41  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.13/0.41  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.13/0.41  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.13/0.41  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.13/0.41  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.13/0.41  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.13/0.41  fof(antisymmetry_r2_hidden, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 0.13/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.41  fof(c_0_22, plain, ![X61]:k1_ordinal1(X61)=k2_xboole_0(X61,k1_tarski(X61)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.13/0.41  fof(c_0_23, plain, ![X43]:k2_tarski(X43,X43)=k1_tarski(X43), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.41  fof(c_0_24, plain, ![X55, X56]:k3_tarski(k2_tarski(X55,X56))=k2_xboole_0(X55,X56), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.13/0.41  fof(c_0_25, plain, ![X44, X45]:k1_enumset1(X44,X44,X45)=k2_tarski(X44,X45), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.41  fof(c_0_26, negated_conjecture, ~(![X1, X2]:(k1_ordinal1(X1)=k1_ordinal1(X2)=>X1=X2)), inference(assume_negation,[status(cth)],[t12_ordinal1])).
% 0.13/0.41  fof(c_0_27, plain, ![X62]:r2_hidden(X62,k1_ordinal1(X62)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 0.13/0.41  cnf(c_0_28, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.41  cnf(c_0_29, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.41  cnf(c_0_30, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.41  cnf(c_0_31, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.41  fof(c_0_32, plain, ![X46, X47, X48]:k2_enumset1(X46,X46,X47,X48)=k1_enumset1(X46,X47,X48), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.41  fof(c_0_33, plain, ![X49, X50, X51, X52]:k3_enumset1(X49,X49,X50,X51,X52)=k2_enumset1(X49,X50,X51,X52), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.41  fof(c_0_34, negated_conjecture, (k1_ordinal1(esk3_0)=k1_ordinal1(esk4_0)&esk3_0!=esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 0.13/0.41  fof(c_0_35, plain, ![X23, X24, X25]:(~r1_tarski(X23,k2_xboole_0(X24,X25))|r1_tarski(k4_xboole_0(X23,X24),X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.13/0.41  fof(c_0_36, plain, ![X34, X35]:k2_tarski(X34,X35)=k2_tarski(X35,X34), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.13/0.41  fof(c_0_37, plain, ![X53, X54]:((~r1_tarski(k1_tarski(X53),X54)|r2_hidden(X53,X54))&(~r2_hidden(X53,X54)|r1_tarski(k1_tarski(X53),X54))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.13/0.41  cnf(c_0_38, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.41  cnf(c_0_39, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.41  cnf(c_0_40, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.41  cnf(c_0_41, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.41  cnf(c_0_42, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.41  cnf(c_0_43, negated_conjecture, (k1_ordinal1(esk3_0)=k1_ordinal1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.41  cnf(c_0_44, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.41  cnf(c_0_45, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.41  cnf(c_0_46, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.41  cnf(c_0_47, plain, (r2_hidden(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,k3_enumset1(X1,X1,X1,X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39]), c_0_31]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42])).
% 0.13/0.41  cnf(c_0_48, negated_conjecture, (k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))=k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_39]), c_0_39]), c_0_31]), c_0_31]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_42])).
% 0.13/0.41  fof(c_0_49, plain, ![X59, X60]:k1_setfam_1(k2_tarski(X59,X60))=k3_xboole_0(X59,X60), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.13/0.41  cnf(c_0_50, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_40]), c_0_41]), c_0_42])).
% 0.13/0.41  cnf(c_0_51, plain, (k3_enumset1(X1,X1,X1,X1,X2)=k3_enumset1(X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_31]), c_0_31]), c_0_41]), c_0_41]), c_0_42]), c_0_42])).
% 0.13/0.41  cnf(c_0_52, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_29]), c_0_31]), c_0_41]), c_0_42])).
% 0.13/0.41  cnf(c_0_53, negated_conjecture, (r2_hidden(esk3_0,k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.13/0.41  fof(c_0_54, plain, ![X57, X58]:((k4_xboole_0(X57,k1_tarski(X58))!=X57|~r2_hidden(X58,X57))&(r2_hidden(X58,X57)|k4_xboole_0(X57,k1_tarski(X58))=X57)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.13/0.41  fof(c_0_55, plain, ![X30, X31]:r1_tarski(X30,k2_xboole_0(X30,X31)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.13/0.41  fof(c_0_56, plain, ![X28, X29]:k2_xboole_0(k3_xboole_0(X28,X29),k4_xboole_0(X28,X29))=X28, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.13/0.41  cnf(c_0_57, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.13/0.41  fof(c_0_58, plain, ![X26, X27]:k4_xboole_0(X26,k4_xboole_0(X26,X27))=k3_xboole_0(X26,X27), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.13/0.41  fof(c_0_59, plain, ![X36, X37, X38, X39, X40, X41]:(((~r2_hidden(X38,X37)|X38=X36|X37!=k1_tarski(X36))&(X39!=X36|r2_hidden(X39,X37)|X37!=k1_tarski(X36)))&((~r2_hidden(esk2_2(X40,X41),X41)|esk2_2(X40,X41)!=X40|X41=k1_tarski(X40))&(r2_hidden(esk2_2(X40,X41),X41)|esk2_2(X40,X41)=X40|X41=k1_tarski(X40)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.13/0.41  cnf(c_0_60, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2)))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.13/0.41  cnf(c_0_61, negated_conjecture, (r1_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.13/0.41  cnf(c_0_62, plain, (r2_hidden(X1,X2)|k4_xboole_0(X2,k1_tarski(X1))=X2), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.13/0.41  fof(c_0_63, plain, ![X63, X64]:(~r2_hidden(X63,X64)|~r1_tarski(X64,X63)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.13/0.41  cnf(c_0_64, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.13/0.41  cnf(c_0_65, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.13/0.41  cnf(c_0_66, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_57, c_0_31])).
% 0.13/0.41  cnf(c_0_67, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.13/0.41  cnf(c_0_68, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.13/0.41  cnf(c_0_69, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.41  cnf(c_0_70, negated_conjecture, (r1_tarski(k4_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)),esk4_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.13/0.41  cnf(c_0_71, plain, (k4_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1))=X2|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_29]), c_0_31]), c_0_41]), c_0_42])).
% 0.13/0.41  cnf(c_0_72, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.13/0.41  cnf(c_0_73, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_40]), c_0_41]), c_0_42])).
% 0.13/0.41  cnf(c_0_74, plain, (k3_tarski(k3_enumset1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_40]), c_0_66]), c_0_66]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_42])).
% 0.13/0.41  cnf(c_0_75, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_66]), c_0_41]), c_0_42])).
% 0.13/0.41  fof(c_0_76, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k4_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k4_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.13/0.41  cnf(c_0_77, plain, (X1=X3|X2!=k3_enumset1(X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_29]), c_0_31]), c_0_41]), c_0_42])).
% 0.13/0.41  cnf(c_0_78, plain, (r2_hidden(X1,X2)|~r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_29]), c_0_31]), c_0_41]), c_0_42])).
% 0.13/0.41  cnf(c_0_79, negated_conjecture, (r1_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)|r2_hidden(esk4_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.13/0.41  cnf(c_0_80, plain, (~r2_hidden(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X1)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.13/0.41  cnf(c_0_81, plain, (k3_tarski(k3_enumset1(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_75]), c_0_75]), c_0_75]), c_0_75]), c_0_51])).
% 0.13/0.41  cnf(c_0_82, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.13/0.41  cnf(c_0_83, plain, (X1=X2|~r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_77])).
% 0.13/0.41  cnf(c_0_84, negated_conjecture, (r2_hidden(esk4_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))|r2_hidden(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.13/0.41  cnf(c_0_85, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.41  fof(c_0_86, plain, ![X21, X22]:(~r1_tarski(X21,X22)|k3_xboole_0(X21,X22)=X21), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.13/0.41  cnf(c_0_87, negated_conjecture, (r1_tarski(esk3_0,k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))))), inference(spm,[status(thm)],[c_0_73, c_0_48])).
% 0.13/0.41  cnf(c_0_88, plain, (~r2_hidden(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.13/0.41  cnf(c_0_89, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_51]), c_0_75])).
% 0.13/0.41  cnf(c_0_90, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_82])).
% 0.13/0.41  cnf(c_0_91, negated_conjecture, (r2_hidden(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85])).
% 0.13/0.41  cnf(c_0_92, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.13/0.41  cnf(c_0_93, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)),esk4_0)), inference(spm,[status(thm)],[c_0_60, c_0_87])).
% 0.13/0.41  cnf(c_0_94, plain, (~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.13/0.41  cnf(c_0_95, negated_conjecture, (r2_hidden(esk3_0,k4_xboole_0(esk4_0,X1))|r2_hidden(esk3_0,X1)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.13/0.41  cnf(c_0_96, plain, (k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_66]), c_0_41]), c_0_42])).
% 0.13/0.41  cnf(c_0_97, negated_conjecture, (r1_tarski(esk3_0,esk4_0)|r2_hidden(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_93, c_0_71])).
% 0.13/0.41  fof(c_0_98, plain, ![X5, X6]:(~r2_hidden(X5,X6)|~r2_hidden(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).
% 0.13/0.41  fof(c_0_99, plain, ![X19, X20]:(((r1_tarski(X19,X20)|X19!=X20)&(r1_tarski(X20,X19)|X19!=X20))&(~r1_tarski(X19,X20)|~r1_tarski(X20,X19)|X19=X20)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.41  cnf(c_0_100, negated_conjecture, (r2_hidden(esk3_0,k4_xboole_0(esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.13/0.41  cnf(c_0_101, negated_conjecture, (r1_tarski(k4_xboole_0(X1,esk3_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))|~r1_tarski(X1,k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))))), inference(spm,[status(thm)],[c_0_50, c_0_48])).
% 0.13/0.41  cnf(c_0_102, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0))=esk3_0|r2_hidden(esk4_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_51]), c_0_75])).
% 0.13/0.41  cnf(c_0_103, plain, (~r2_hidden(X1,X2)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.13/0.41  cnf(c_0_104, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_99])).
% 0.13/0.41  cnf(c_0_105, negated_conjecture, (r1_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k4_xboole_0(esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_52, c_0_100])).
% 0.13/0.41  cnf(c_0_106, negated_conjecture, (r1_tarski(k4_xboole_0(esk4_0,esk3_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_101, c_0_73])).
% 0.13/0.41  cnf(c_0_107, negated_conjecture, (k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k4_xboole_0(esk4_0,esk3_0)))=esk4_0|r2_hidden(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_81, c_0_102])).
% 0.13/0.41  cnf(c_0_108, negated_conjecture, (~r2_hidden(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_103, c_0_91])).
% 0.13/0.41  cnf(c_0_109, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_99])).
% 0.13/0.41  cnf(c_0_110, negated_conjecture, (k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k4_xboole_0(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_106])])).
% 0.13/0.41  cnf(c_0_111, negated_conjecture, (k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k4_xboole_0(esk4_0,esk3_0)))=esk4_0), inference(sr,[status(thm)],[c_0_107, c_0_108])).
% 0.13/0.41  cnf(c_0_112, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_109])).
% 0.13/0.41  cnf(c_0_113, negated_conjecture, (k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_110]), c_0_111])).
% 0.13/0.41  cnf(c_0_114, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_72, c_0_112])).
% 0.13/0.41  cnf(c_0_115, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_113]), c_0_114]), ['proof']).
% 0.13/0.41  # SZS output end CNFRefutation
% 0.13/0.41  # Proof object total steps             : 116
% 0.13/0.41  # Proof object clause steps            : 71
% 0.13/0.41  # Proof object formula steps           : 45
% 0.13/0.41  # Proof object conjectures             : 27
% 0.13/0.41  # Proof object clause conjectures      : 24
% 0.13/0.41  # Proof object formula conjectures     : 3
% 0.13/0.41  # Proof object initial clauses used    : 25
% 0.13/0.41  # Proof object initial formulas used   : 22
% 0.13/0.41  # Proof object generating inferences   : 25
% 0.13/0.41  # Proof object simplifying inferences  : 86
% 0.13/0.41  # Training examples: 0 positive, 0 negative
% 0.13/0.41  # Parsed axioms                        : 24
% 0.13/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.41  # Initial clauses                      : 41
% 0.13/0.41  # Removed in clause preprocessing      : 9
% 0.13/0.41  # Initial clauses in saturation        : 32
% 0.13/0.41  # Processed clauses                    : 586
% 0.13/0.41  # ...of these trivial                  : 28
% 0.13/0.41  # ...subsumed                          : 361
% 0.13/0.41  # ...remaining for further processing  : 197
% 0.13/0.41  # Other redundant clauses eliminated   : 23
% 0.13/0.41  # Clauses deleted for lack of memory   : 0
% 0.13/0.41  # Backward-subsumed                    : 3
% 0.13/0.41  # Backward-rewritten                   : 47
% 0.13/0.41  # Generated clauses                    : 2092
% 0.13/0.41  # ...of the previous two non-trivial   : 1753
% 0.13/0.41  # Contextual simplify-reflections      : 2
% 0.13/0.41  # Paramodulations                      : 2066
% 0.13/0.41  # Factorizations                       : 0
% 0.13/0.41  # Equation resolutions                 : 24
% 0.13/0.41  # Propositional unsat checks           : 0
% 0.13/0.41  #    Propositional check models        : 0
% 0.13/0.41  #    Propositional check unsatisfiable : 0
% 0.13/0.41  #    Propositional clauses             : 0
% 0.13/0.41  #    Propositional clauses after purity: 0
% 0.13/0.41  #    Propositional unsat core size     : 0
% 0.13/0.41  #    Propositional preprocessing time  : 0.000
% 0.13/0.41  #    Propositional encoding time       : 0.000
% 0.13/0.41  #    Propositional solver time         : 0.000
% 0.13/0.41  #    Success case prop preproc time    : 0.000
% 0.13/0.41  #    Success case prop encoding time   : 0.000
% 0.13/0.41  #    Success case prop solver time     : 0.000
% 0.13/0.41  # Current number of processed clauses  : 106
% 0.13/0.41  #    Positive orientable unit clauses  : 32
% 0.13/0.41  #    Positive unorientable unit clauses: 3
% 0.13/0.41  #    Negative unit clauses             : 22
% 0.13/0.41  #    Non-unit-clauses                  : 49
% 0.13/0.41  # Current number of unprocessed clauses: 1220
% 0.13/0.41  # ...number of literals in the above   : 3170
% 0.13/0.41  # Current number of archived formulas  : 0
% 0.13/0.41  # Current number of archived clauses   : 91
% 0.13/0.41  # Clause-clause subsumption calls (NU) : 899
% 0.13/0.41  # Rec. Clause-clause subsumption calls : 760
% 0.13/0.41  # Non-unit clause-clause subsumptions  : 67
% 0.13/0.41  # Unit Clause-clause subsumption calls : 395
% 0.13/0.41  # Rewrite failures with RHS unbound    : 3
% 0.13/0.41  # BW rewrite match attempts            : 183
% 0.13/0.41  # BW rewrite match successes           : 74
% 0.13/0.41  # Condensation attempts                : 0
% 0.13/0.41  # Condensation successes               : 0
% 0.13/0.41  # Termbank termtop insertions          : 26126
% 0.13/0.42  
% 0.13/0.42  # -------------------------------------------------
% 0.13/0.42  # User time                : 0.066 s
% 0.13/0.42  # System time              : 0.004 s
% 0.13/0.42  # Total time               : 0.070 s
% 0.13/0.42  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
