%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:44 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  129 (6622 expanded)
%              Number of clauses        :   80 (2650 expanded)
%              Number of leaves         :   24 (1956 expanded)
%              Depth                    :   21
%              Number of atoms          :  216 (9254 expanded)
%              Number of equality atoms :  127 (7147 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t29_xboole_1,axiom,(
    ! [X1,X2,X3] : r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(l98_xboole_1,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(c_0_24,plain,(
    ! [X74,X75] : k3_tarski(k2_tarski(X74,X75)) = k2_xboole_0(X74,X75) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_25,plain,(
    ! [X48,X49] : k1_enumset1(X48,X48,X49) = k2_tarski(X48,X49) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_xboole_0
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t43_zfmisc_1])).

fof(c_0_27,plain,(
    ! [X15,X16,X17,X18,X19] :
      ( ( ~ r1_tarski(X15,X16)
        | ~ r2_hidden(X17,X15)
        | r2_hidden(X17,X16) )
      & ( r2_hidden(esk2_2(X18,X19),X18)
        | r1_tarski(X18,X19) )
      & ( ~ r2_hidden(esk2_2(X18,X19),X19)
        | r1_tarski(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_28,plain,(
    ! [X37,X38,X39] : r1_tarski(k3_xboole_0(X37,X38),k2_xboole_0(X37,X39)) ),
    inference(variable_rename,[status(thm)],[t29_xboole_1])).

cnf(c_0_29,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_31,plain,(
    ! [X50,X51,X52] : k2_enumset1(X50,X50,X51,X52) = k1_enumset1(X50,X51,X52) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_32,plain,(
    ! [X53,X54,X55,X56] : k3_enumset1(X53,X53,X54,X55,X56) = k2_enumset1(X53,X54,X55,X56) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_33,plain,(
    ! [X57,X58,X59,X60,X61] : k4_enumset1(X57,X57,X58,X59,X60,X61) = k3_enumset1(X57,X58,X59,X60,X61) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_34,plain,(
    ! [X62,X63,X64,X65,X66,X67] : k5_enumset1(X62,X62,X63,X64,X65,X66,X67) = k4_enumset1(X62,X63,X64,X65,X66,X67) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_35,negated_conjecture,
    ( k1_tarski(esk4_0) = k2_xboole_0(esk5_0,esk6_0)
    & ( esk5_0 != k1_tarski(esk4_0)
      | esk6_0 != k1_tarski(esk4_0) )
    & ( esk5_0 != k1_xboole_0
      | esk6_0 != k1_tarski(esk4_0) )
    & ( esk5_0 != k1_tarski(esk4_0)
      | esk6_0 != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

fof(c_0_36,plain,(
    ! [X47] : k2_tarski(X47,X47) = k1_tarski(X47) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_37,plain,(
    ! [X35,X36] :
      ( ~ r1_tarski(X35,X36)
      | k3_xboole_0(X35,X36) = X35 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_40,plain,(
    ! [X29,X30] : k5_xboole_0(X29,X30) = k4_xboole_0(k2_xboole_0(X29,X30),k3_xboole_0(X29,X30)) ),
    inference(variable_rename,[status(thm)],[l98_xboole_1])).

fof(c_0_41,plain,(
    ! [X31,X32] : k4_xboole_0(X31,X32) = k5_xboole_0(X31,k3_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_42,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_44,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( k1_tarski(esk4_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_49,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_50,plain,(
    ! [X21,X22] :
      ( ( ~ r1_xboole_0(X21,X22)
        | k3_xboole_0(X21,X22) = k1_xboole_0 )
      & ( k3_xboole_0(X21,X22) != k1_xboole_0
        | r1_xboole_0(X21,X22) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_53,plain,(
    ! [X40] : k5_xboole_0(X40,k1_xboole_0) = X40 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_54,plain,(
    ! [X9,X10] : k5_xboole_0(X9,X10) = k5_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_57,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_58,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_59,negated_conjecture,
    ( k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k3_tarski(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_30]),c_0_43]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_47]),c_0_47])).

fof(c_0_60,plain,(
    ! [X23,X24,X26,X27,X28] :
      ( ( r1_xboole_0(X23,X24)
        | r2_hidden(esk3_2(X23,X24),k3_xboole_0(X23,X24)) )
      & ( ~ r2_hidden(X28,k3_xboole_0(X26,X27))
        | ~ r1_xboole_0(X26,X27) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_61,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_62,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

fof(c_0_63,plain,(
    ! [X43,X44,X45] : k5_xboole_0(k5_xboole_0(X43,X44),X45) = k5_xboole_0(X43,k5_xboole_0(X44,X45)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_64,plain,(
    ! [X46] : k5_xboole_0(X46,X46) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_65,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_66,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)),k3_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)),k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_43]),c_0_56]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_47]),c_0_47])).

cnf(c_0_68,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk5_0,X1),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

fof(c_0_70,plain,(
    ! [X41,X42] : r1_tarski(X41,k2_xboole_0(X41,X42)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_71,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_72,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62])])).

fof(c_0_73,plain,(
    ! [X72,X73] :
      ( ( ~ r1_tarski(X72,k1_tarski(X73))
        | X72 = k1_xboole_0
        | X72 = k1_tarski(X73) )
      & ( X72 != k1_xboole_0
        | r1_tarski(X72,k1_tarski(X73)) )
      & ( X72 != k1_tarski(X73)
        | r1_tarski(X72,k1_tarski(X73)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_74,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_75,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_76,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_77,plain,
    ( k5_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)),k3_xboole_0(k3_xboole_0(X1,X2),k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_78,negated_conjecture,
    ( k3_xboole_0(k3_xboole_0(esk5_0,X1),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) = k3_xboole_0(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_69])).

cnf(c_0_79,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_80,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_62])).

cnf(c_0_81,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_82,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])).

cnf(c_0_83,negated_conjecture,
    ( k5_xboole_0(k3_xboole_0(esk5_0,esk6_0),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) = k5_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_59]),c_0_78]),c_0_66])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_85,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_39])).

cnf(c_0_86,plain,
    ( X1 = k1_xboole_0
    | X1 = k5_enumset1(X2,X2,X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_49]),c_0_49]),c_0_30]),c_0_30]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_47]),c_0_47])).

cnf(c_0_87,negated_conjecture,
    ( k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,k3_xboole_0(esk5_0,esk6_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_66]),c_0_74])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(esk5_0,k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_59])).

cnf(c_0_89,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_85])).

cnf(c_0_90,negated_conjecture,
    ( X1 = k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,k3_xboole_0(esk5_0,esk6_0)))
    | X1 = k1_xboole_0
    | ~ r1_tarski(X1,k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,k3_xboole_0(esk5_0,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(esk5_0,k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,k3_xboole_0(esk5_0,esk6_0)))) ),
    inference(rw,[status(thm)],[c_0_88,c_0_87])).

cnf(c_0_92,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_89])).

cnf(c_0_93,negated_conjecture,
    ( k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,k3_xboole_0(esk5_0,esk6_0))) = esk5_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_94,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | esk6_0 != k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_95,plain,
    ( k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_92]),c_0_89]),c_0_65]),c_0_65])).

cnf(c_0_96,negated_conjecture,
    ( k5_xboole_0(esk6_0,k3_xboole_0(esk5_0,esk6_0)) = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_93]),c_0_75])).

cnf(c_0_97,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | esk6_0 != k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_49]),c_0_30]),c_0_44]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_98,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk6_0) = esk6_0
    | esk5_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_96]),c_0_65])).

fof(c_0_100,plain,(
    ! [X70,X71] :
      ( r2_hidden(X70,X71)
      | r1_xboole_0(k1_tarski(X70),X71) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

cnf(c_0_101,negated_conjecture,
    ( k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,k3_xboole_0(esk5_0,esk6_0))) != esk6_0
    | esk5_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_97,c_0_87])).

cnf(c_0_102,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_103,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_89]),c_0_65]),c_0_76])])).

cnf(c_0_105,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_49]),c_0_30]),c_0_44]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_106,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk6_0) = esk6_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_104]),c_0_68])).

cnf(c_0_107,negated_conjecture,
    ( esk5_0 != k1_tarski(esk4_0)
    | esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_108,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_109,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk3_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_110,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X3,k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_105])).

cnf(c_0_111,negated_conjecture,
    ( k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_106]),c_0_75]),c_0_65])).

cnf(c_0_112,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | esk5_0 != k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107,c_0_49]),c_0_30]),c_0_44]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_113,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk3_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

fof(c_0_114,plain,(
    ! [X68,X69] :
      ( ( ~ r1_tarski(k1_tarski(X68),X69)
        | r2_hidden(X68,X69) )
      & ( ~ r2_hidden(X68,X69)
        | r1_tarski(k1_tarski(X68),X69) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_115,negated_conjecture,
    ( r2_hidden(esk4_0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_116,negated_conjecture,
    ( k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,k3_xboole_0(esk5_0,esk6_0))) != esk5_0
    | esk6_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_112,c_0_87])).

cnf(c_0_117,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk3_2(X1,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_113]),c_0_62])).

cnf(c_0_118,negated_conjecture,
    ( esk5_0 != k1_tarski(esk4_0)
    | esk6_0 != k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_119,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_114])).

cnf(c_0_120,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_115,c_0_106])).

cnf(c_0_121,negated_conjecture,
    ( r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_92]),c_0_76]),c_0_65])])).

cnf(c_0_122,negated_conjecture,
    ( esk5_0 != k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)
    | esk6_0 != k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_118,c_0_49]),c_0_49]),c_0_30]),c_0_30]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_47]),c_0_47])).

cnf(c_0_123,plain,
    ( r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_49]),c_0_30]),c_0_44]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_124,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_120,c_0_121])).

cnf(c_0_125,negated_conjecture,
    ( k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,k3_xboole_0(esk5_0,esk6_0))) != esk5_0
    | k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,k3_xboole_0(esk5_0,esk6_0))) != esk6_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_122,c_0_87]),c_0_87])).

cnf(c_0_126,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_124]),c_0_87]),c_0_106]),c_0_75]),c_0_65])).

cnf(c_0_127,negated_conjecture,
    ( esk6_0 != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_125,c_0_106]),c_0_75]),c_0_65]),c_0_106]),c_0_75]),c_0_65])])).

cnf(c_0_128,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_126]),c_0_106]),c_0_127]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:26:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.45  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.21/0.45  # and selection function SelectNegativeLiterals.
% 0.21/0.45  #
% 0.21/0.45  # Preprocessing time       : 0.028 s
% 0.21/0.45  # Presaturation interreduction done
% 0.21/0.45  
% 0.21/0.45  # Proof found!
% 0.21/0.45  # SZS status Theorem
% 0.21/0.45  # SZS output start CNFRefutation
% 0.21/0.45  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.21/0.45  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.45  fof(t43_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 0.21/0.45  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.45  fof(t29_xboole_1, axiom, ![X1, X2, X3]:r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_xboole_1)).
% 0.21/0.45  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.45  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.21/0.45  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.21/0.45  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.21/0.45  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.45  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.21/0.45  fof(l98_xboole_1, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 0.21/0.45  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.21/0.45  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.21/0.45  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.21/0.45  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.21/0.45  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.21/0.45  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.21/0.45  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.21/0.45  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.21/0.45  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.21/0.45  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.21/0.45  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.21/0.45  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.21/0.45  fof(c_0_24, plain, ![X74, X75]:k3_tarski(k2_tarski(X74,X75))=k2_xboole_0(X74,X75), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.21/0.45  fof(c_0_25, plain, ![X48, X49]:k1_enumset1(X48,X48,X49)=k2_tarski(X48,X49), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.45  fof(c_0_26, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0))))), inference(assume_negation,[status(cth)],[t43_zfmisc_1])).
% 0.21/0.45  fof(c_0_27, plain, ![X15, X16, X17, X18, X19]:((~r1_tarski(X15,X16)|(~r2_hidden(X17,X15)|r2_hidden(X17,X16)))&((r2_hidden(esk2_2(X18,X19),X18)|r1_tarski(X18,X19))&(~r2_hidden(esk2_2(X18,X19),X19)|r1_tarski(X18,X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.45  fof(c_0_28, plain, ![X37, X38, X39]:r1_tarski(k3_xboole_0(X37,X38),k2_xboole_0(X37,X39)), inference(variable_rename,[status(thm)],[t29_xboole_1])).
% 0.21/0.45  cnf(c_0_29, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.45  cnf(c_0_30, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.45  fof(c_0_31, plain, ![X50, X51, X52]:k2_enumset1(X50,X50,X51,X52)=k1_enumset1(X50,X51,X52), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.45  fof(c_0_32, plain, ![X53, X54, X55, X56]:k3_enumset1(X53,X53,X54,X55,X56)=k2_enumset1(X53,X54,X55,X56), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.21/0.45  fof(c_0_33, plain, ![X57, X58, X59, X60, X61]:k4_enumset1(X57,X57,X58,X59,X60,X61)=k3_enumset1(X57,X58,X59,X60,X61), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.21/0.45  fof(c_0_34, plain, ![X62, X63, X64, X65, X66, X67]:k5_enumset1(X62,X62,X63,X64,X65,X66,X67)=k4_enumset1(X62,X63,X64,X65,X66,X67), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.21/0.45  fof(c_0_35, negated_conjecture, (((k1_tarski(esk4_0)=k2_xboole_0(esk5_0,esk6_0)&(esk5_0!=k1_tarski(esk4_0)|esk6_0!=k1_tarski(esk4_0)))&(esk5_0!=k1_xboole_0|esk6_0!=k1_tarski(esk4_0)))&(esk5_0!=k1_tarski(esk4_0)|esk6_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 0.21/0.45  fof(c_0_36, plain, ![X47]:k2_tarski(X47,X47)=k1_tarski(X47), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.45  fof(c_0_37, plain, ![X35, X36]:(~r1_tarski(X35,X36)|k3_xboole_0(X35,X36)=X35), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.21/0.45  cnf(c_0_38, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.45  cnf(c_0_39, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.45  fof(c_0_40, plain, ![X29, X30]:k5_xboole_0(X29,X30)=k4_xboole_0(k2_xboole_0(X29,X30),k3_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[l98_xboole_1])).
% 0.21/0.45  fof(c_0_41, plain, ![X31, X32]:k4_xboole_0(X31,X32)=k5_xboole_0(X31,k3_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.21/0.45  cnf(c_0_42, plain, (r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.45  cnf(c_0_43, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.21/0.45  cnf(c_0_44, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.45  cnf(c_0_45, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.45  cnf(c_0_46, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.45  cnf(c_0_47, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.45  cnf(c_0_48, negated_conjecture, (k1_tarski(esk4_0)=k2_xboole_0(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.45  cnf(c_0_49, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.45  fof(c_0_50, plain, ![X21, X22]:((~r1_xboole_0(X21,X22)|k3_xboole_0(X21,X22)=k1_xboole_0)&(k3_xboole_0(X21,X22)!=k1_xboole_0|r1_xboole_0(X21,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.21/0.45  cnf(c_0_51, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.45  cnf(c_0_52, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.21/0.45  fof(c_0_53, plain, ![X40]:k5_xboole_0(X40,k1_xboole_0)=X40, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.21/0.45  fof(c_0_54, plain, ![X9, X10]:k5_xboole_0(X9,X10)=k5_xboole_0(X10,X9), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.21/0.45  cnf(c_0_55, plain, (k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.45  cnf(c_0_56, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.45  fof(c_0_57, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.21/0.45  cnf(c_0_58, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])).
% 0.21/0.45  cnf(c_0_59, negated_conjecture, (k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k3_tarski(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49]), c_0_30]), c_0_43]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_47]), c_0_47])).
% 0.21/0.45  fof(c_0_60, plain, ![X23, X24, X26, X27, X28]:((r1_xboole_0(X23,X24)|r2_hidden(esk3_2(X23,X24),k3_xboole_0(X23,X24)))&(~r2_hidden(X28,k3_xboole_0(X26,X27))|~r1_xboole_0(X26,X27))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.21/0.45  cnf(c_0_61, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.45  cnf(c_0_62, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.21/0.45  fof(c_0_63, plain, ![X43, X44, X45]:k5_xboole_0(k5_xboole_0(X43,X44),X45)=k5_xboole_0(X43,k5_xboole_0(X44,X45)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.21/0.45  fof(c_0_64, plain, ![X46]:k5_xboole_0(X46,X46)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.21/0.45  cnf(c_0_65, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.21/0.45  cnf(c_0_66, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.21/0.45  cnf(c_0_67, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)),k3_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)),k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_43]), c_0_56]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_47]), c_0_47])).
% 0.21/0.45  cnf(c_0_68, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.21/0.45  cnf(c_0_69, negated_conjecture, (r1_tarski(k3_xboole_0(esk5_0,X1),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.21/0.45  fof(c_0_70, plain, ![X41, X42]:r1_tarski(X41,k2_xboole_0(X41,X42)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.21/0.45  cnf(c_0_71, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.21/0.45  cnf(c_0_72, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62])])).
% 0.21/0.45  fof(c_0_73, plain, ![X72, X73]:((~r1_tarski(X72,k1_tarski(X73))|(X72=k1_xboole_0|X72=k1_tarski(X73)))&((X72!=k1_xboole_0|r1_tarski(X72,k1_tarski(X73)))&(X72!=k1_tarski(X73)|r1_tarski(X72,k1_tarski(X73))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.21/0.45  cnf(c_0_74, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.21/0.45  cnf(c_0_75, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.21/0.45  cnf(c_0_76, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.21/0.45  cnf(c_0_77, plain, (k5_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)),k3_xboole_0(k3_xboole_0(X1,X2),k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_67, c_0_68])).
% 0.21/0.45  cnf(c_0_78, negated_conjecture, (k3_xboole_0(k3_xboole_0(esk5_0,X1),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))=k3_xboole_0(esk5_0,X1)), inference(spm,[status(thm)],[c_0_51, c_0_69])).
% 0.21/0.45  cnf(c_0_79, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.21/0.45  cnf(c_0_80, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_62])).
% 0.21/0.45  cnf(c_0_81, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.21/0.45  cnf(c_0_82, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])).
% 0.21/0.45  cnf(c_0_83, negated_conjecture, (k5_xboole_0(k3_xboole_0(esk5_0,esk6_0),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))=k5_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_59]), c_0_78]), c_0_66])).
% 0.21/0.45  cnf(c_0_84, plain, (r1_tarski(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])).
% 0.21/0.45  cnf(c_0_85, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_80, c_0_39])).
% 0.21/0.45  cnf(c_0_86, plain, (X1=k1_xboole_0|X1=k5_enumset1(X2,X2,X2,X2,X2,X2,X2)|~r1_tarski(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_49]), c_0_49]), c_0_30]), c_0_30]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_47]), c_0_47])).
% 0.21/0.45  cnf(c_0_87, negated_conjecture, (k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,k3_xboole_0(esk5_0,esk6_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_66]), c_0_74])).
% 0.21/0.45  cnf(c_0_88, negated_conjecture, (r1_tarski(esk5_0,k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_84, c_0_59])).
% 0.21/0.45  cnf(c_0_89, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_85])).
% 0.21/0.45  cnf(c_0_90, negated_conjecture, (X1=k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,k3_xboole_0(esk5_0,esk6_0)))|X1=k1_xboole_0|~r1_tarski(X1,k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,k3_xboole_0(esk5_0,esk6_0))))), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.21/0.45  cnf(c_0_91, negated_conjecture, (r1_tarski(esk5_0,k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,k3_xboole_0(esk5_0,esk6_0))))), inference(rw,[status(thm)],[c_0_88, c_0_87])).
% 0.21/0.45  cnf(c_0_92, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_89])).
% 0.21/0.45  cnf(c_0_93, negated_conjecture, (k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,k3_xboole_0(esk5_0,esk6_0)))=esk5_0|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.21/0.45  cnf(c_0_94, negated_conjecture, (esk5_0!=k1_xboole_0|esk6_0!=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.45  cnf(c_0_95, plain, (k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_92]), c_0_89]), c_0_65]), c_0_65])).
% 0.21/0.45  cnf(c_0_96, negated_conjecture, (k5_xboole_0(esk6_0,k3_xboole_0(esk5_0,esk6_0))=k1_xboole_0|esk5_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_93]), c_0_75])).
% 0.21/0.45  cnf(c_0_97, negated_conjecture, (esk5_0!=k1_xboole_0|esk6_0!=k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_49]), c_0_30]), c_0_44]), c_0_45]), c_0_46]), c_0_47])).
% 0.21/0.45  cnf(c_0_98, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_58, c_0_95])).
% 0.21/0.45  cnf(c_0_99, negated_conjecture, (k3_xboole_0(esk5_0,esk6_0)=esk6_0|esk5_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_96]), c_0_65])).
% 0.21/0.45  fof(c_0_100, plain, ![X70, X71]:(r2_hidden(X70,X71)|r1_xboole_0(k1_tarski(X70),X71)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.21/0.45  cnf(c_0_101, negated_conjecture, (k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,k3_xboole_0(esk5_0,esk6_0)))!=esk6_0|esk5_0!=k1_xboole_0), inference(rw,[status(thm)],[c_0_97, c_0_87])).
% 0.21/0.45  cnf(c_0_102, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 0.21/0.45  cnf(c_0_103, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.21/0.45  cnf(c_0_104, negated_conjecture, (r1_tarski(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_89]), c_0_65]), c_0_76])])).
% 0.21/0.45  cnf(c_0_105, plain, (r2_hidden(X1,X2)|r1_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_49]), c_0_30]), c_0_44]), c_0_45]), c_0_46]), c_0_47])).
% 0.21/0.45  cnf(c_0_106, negated_conjecture, (k3_xboole_0(esk5_0,esk6_0)=esk6_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_104]), c_0_68])).
% 0.21/0.45  cnf(c_0_107, negated_conjecture, (esk5_0!=k1_tarski(esk4_0)|esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.45  cnf(c_0_108, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.45  cnf(c_0_109, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk3_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.21/0.45  cnf(c_0_110, plain, (r2_hidden(X1,X2)|~r2_hidden(X3,k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2))), inference(spm,[status(thm)],[c_0_71, c_0_105])).
% 0.21/0.45  cnf(c_0_111, negated_conjecture, (k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_106]), c_0_75]), c_0_65])).
% 0.21/0.45  cnf(c_0_112, negated_conjecture, (esk6_0!=k1_xboole_0|esk5_0!=k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107, c_0_49]), c_0_30]), c_0_44]), c_0_45]), c_0_46]), c_0_47])).
% 0.21/0.45  cnf(c_0_113, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk3_2(X1,X2),k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 0.21/0.45  fof(c_0_114, plain, ![X68, X69]:((~r1_tarski(k1_tarski(X68),X69)|r2_hidden(X68,X69))&(~r2_hidden(X68,X69)|r1_tarski(k1_tarski(X68),X69))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.21/0.45  cnf(c_0_115, negated_conjecture, (r2_hidden(esk4_0,X1)|~r2_hidden(X2,k3_xboole_0(esk5_0,X1))), inference(spm,[status(thm)],[c_0_110, c_0_111])).
% 0.21/0.45  cnf(c_0_116, negated_conjecture, (k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,k3_xboole_0(esk5_0,esk6_0)))!=esk5_0|esk6_0!=k1_xboole_0), inference(rw,[status(thm)],[c_0_112, c_0_87])).
% 0.21/0.45  cnf(c_0_117, plain, (k1_xboole_0=X1|r2_hidden(esk3_2(X1,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_113]), c_0_62])).
% 0.21/0.45  cnf(c_0_118, negated_conjecture, (esk5_0!=k1_tarski(esk4_0)|esk6_0!=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.45  cnf(c_0_119, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_114])).
% 0.21/0.45  cnf(c_0_120, negated_conjecture, (r2_hidden(esk4_0,esk6_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_115, c_0_106])).
% 0.21/0.45  cnf(c_0_121, negated_conjecture, (r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_92]), c_0_76]), c_0_65])])).
% 0.21/0.45  cnf(c_0_122, negated_conjecture, (esk5_0!=k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)|esk6_0!=k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_118, c_0_49]), c_0_49]), c_0_30]), c_0_30]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_47]), c_0_47])).
% 0.21/0.45  cnf(c_0_123, plain, (r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119, c_0_49]), c_0_30]), c_0_44]), c_0_45]), c_0_46]), c_0_47])).
% 0.21/0.45  cnf(c_0_124, negated_conjecture, (r2_hidden(esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_120, c_0_121])).
% 0.21/0.45  cnf(c_0_125, negated_conjecture, (k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,k3_xboole_0(esk5_0,esk6_0)))!=esk5_0|k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,k3_xboole_0(esk5_0,esk6_0)))!=esk6_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_122, c_0_87]), c_0_87])).
% 0.21/0.45  cnf(c_0_126, negated_conjecture, (r1_tarski(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_124]), c_0_87]), c_0_106]), c_0_75]), c_0_65])).
% 0.21/0.45  cnf(c_0_127, negated_conjecture, (esk6_0!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_125, c_0_106]), c_0_75]), c_0_65]), c_0_106]), c_0_75]), c_0_65])])).
% 0.21/0.45  cnf(c_0_128, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_126]), c_0_106]), c_0_127]), ['proof']).
% 0.21/0.45  # SZS output end CNFRefutation
% 0.21/0.45  # Proof object total steps             : 129
% 0.21/0.45  # Proof object clause steps            : 80
% 0.21/0.45  # Proof object formula steps           : 49
% 0.21/0.45  # Proof object conjectures             : 35
% 0.21/0.45  # Proof object clause conjectures      : 32
% 0.21/0.45  # Proof object formula conjectures     : 3
% 0.21/0.45  # Proof object initial clauses used    : 30
% 0.21/0.45  # Proof object initial formulas used   : 24
% 0.21/0.45  # Proof object generating inferences   : 32
% 0.21/0.45  # Proof object simplifying inferences  : 124
% 0.21/0.45  # Training examples: 0 positive, 0 negative
% 0.21/0.45  # Parsed axioms                        : 26
% 0.21/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.45  # Initial clauses                      : 37
% 0.21/0.45  # Removed in clause preprocessing      : 8
% 0.21/0.45  # Initial clauses in saturation        : 29
% 0.21/0.45  # Processed clauses                    : 815
% 0.21/0.45  # ...of these trivial                  : 58
% 0.21/0.45  # ...subsumed                          : 467
% 0.21/0.45  # ...remaining for further processing  : 290
% 0.21/0.45  # Other redundant clauses eliminated   : 34
% 0.21/0.45  # Clauses deleted for lack of memory   : 0
% 0.21/0.45  # Backward-subsumed                    : 3
% 0.21/0.45  # Backward-rewritten                   : 94
% 0.21/0.45  # Generated clauses                    : 5045
% 0.21/0.45  # ...of the previous two non-trivial   : 3129
% 0.21/0.45  # Contextual simplify-reflections      : 0
% 0.21/0.45  # Paramodulations                      : 5009
% 0.21/0.45  # Factorizations                       : 2
% 0.21/0.45  # Equation resolutions                 : 34
% 0.21/0.45  # Propositional unsat checks           : 0
% 0.21/0.45  #    Propositional check models        : 0
% 0.21/0.45  #    Propositional check unsatisfiable : 0
% 0.21/0.45  #    Propositional clauses             : 0
% 0.21/0.45  #    Propositional clauses after purity: 0
% 0.21/0.45  #    Propositional unsat core size     : 0
% 0.21/0.45  #    Propositional preprocessing time  : 0.000
% 0.21/0.45  #    Propositional encoding time       : 0.000
% 0.21/0.45  #    Propositional solver time         : 0.000
% 0.21/0.45  #    Success case prop preproc time    : 0.000
% 0.21/0.45  #    Success case prop encoding time   : 0.000
% 0.21/0.45  #    Success case prop solver time     : 0.000
% 0.21/0.45  # Current number of processed clauses  : 162
% 0.21/0.45  #    Positive orientable unit clauses  : 58
% 0.21/0.45  #    Positive unorientable unit clauses: 4
% 0.21/0.45  #    Negative unit clauses             : 3
% 0.21/0.45  #    Non-unit-clauses                  : 97
% 0.21/0.45  # Current number of unprocessed clauses: 2224
% 0.21/0.45  # ...number of literals in the above   : 4658
% 0.21/0.45  # Current number of archived formulas  : 0
% 0.21/0.45  # Current number of archived clauses   : 134
% 0.21/0.45  # Clause-clause subsumption calls (NU) : 3573
% 0.21/0.45  # Rec. Clause-clause subsumption calls : 3408
% 0.21/0.45  # Non-unit clause-clause subsumptions  : 372
% 0.21/0.45  # Unit Clause-clause subsumption calls : 242
% 0.21/0.45  # Rewrite failures with RHS unbound    : 0
% 0.21/0.45  # BW rewrite match attempts            : 132
% 0.21/0.45  # BW rewrite match successes           : 52
% 0.21/0.45  # Condensation attempts                : 0
% 0.21/0.45  # Condensation successes               : 0
% 0.21/0.45  # Termbank termtop insertions          : 62731
% 0.21/0.45  
% 0.21/0.45  # -------------------------------------------------
% 0.21/0.45  # User time                : 0.093 s
% 0.21/0.45  # System time              : 0.004 s
% 0.21/0.45  # Total time               : 0.097 s
% 0.21/0.45  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
