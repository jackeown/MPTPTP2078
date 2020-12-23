%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:53 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  114 (8436 expanded)
%              Number of clauses        :   67 (3150 expanded)
%              Number of leaves         :   23 (2602 expanded)
%              Depth                    :   17
%              Number of atoms          :  242 (11079 expanded)
%              Number of equality atoms :  131 (9972 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

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

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

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

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_23,plain,(
    ! [X65,X66] : k3_tarski(k2_tarski(X65,X66)) = k2_xboole_0(X65,X66) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_24,plain,(
    ! [X32,X33] : k1_enumset1(X32,X32,X33) = k2_tarski(X32,X33) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_xboole_0
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t43_zfmisc_1])).

fof(c_0_26,plain,(
    ! [X29,X30] : r1_tarski(X29,k2_xboole_0(X29,X30)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_27,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_29,plain,(
    ! [X34,X35,X36] : k2_enumset1(X34,X34,X35,X36) = k1_enumset1(X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_30,plain,(
    ! [X37,X38,X39,X40] : k3_enumset1(X37,X37,X38,X39,X40) = k2_enumset1(X37,X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_31,plain,(
    ! [X41,X42,X43,X44,X45] : k4_enumset1(X41,X41,X42,X43,X44,X45) = k3_enumset1(X41,X42,X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_32,plain,(
    ! [X46,X47,X48,X49,X50,X51] : k5_enumset1(X46,X46,X47,X48,X49,X50,X51) = k4_enumset1(X46,X47,X48,X49,X50,X51) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_33,plain,(
    ! [X52,X53,X54,X55,X56,X57,X58] : k6_enumset1(X52,X52,X53,X54,X55,X56,X57,X58) = k5_enumset1(X52,X53,X54,X55,X56,X57,X58) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_34,negated_conjecture,
    ( k1_tarski(esk2_0) = k2_xboole_0(esk3_0,esk4_0)
    & ( esk3_0 != k1_tarski(esk2_0)
      | esk4_0 != k1_tarski(esk2_0) )
    & ( esk3_0 != k1_xboole_0
      | esk4_0 != k1_tarski(esk2_0) )
    & ( esk3_0 != k1_tarski(esk2_0)
      | esk4_0 != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

fof(c_0_35,plain,(
    ! [X31] : k2_tarski(X31,X31) = k1_tarski(X31) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_36,plain,(
    ! [X63,X64] :
      ( ( ~ r1_tarski(X63,k1_tarski(X64))
        | X63 = k1_xboole_0
        | X63 = k1_tarski(X64) )
      & ( X63 != k1_xboole_0
        | r1_tarski(X63,k1_tarski(X64)) )
      & ( X63 != k1_tarski(X64)
        | r1_tarski(X63,k1_tarski(X64)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_39,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( k1_tarski(esk2_0) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_46,plain,(
    ! [X61,X62] :
      ( r2_hidden(X61,X62)
      | r1_xboole_0(k1_tarski(X61),X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

cnf(c_0_47,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) = k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45]),c_0_28]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43])).

fof(c_0_50,plain,(
    ! [X59,X60] :
      ( ( ~ r1_tarski(k1_tarski(X59),X60)
        | r2_hidden(X59,X60) )
      & ( ~ r2_hidden(X59,X60)
        | r1_tarski(k1_tarski(X59),X60) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,plain,
    ( X1 = k1_xboole_0
    | X1 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_45]),c_0_45]),c_0_28]),c_0_28]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk3_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

fof(c_0_54,plain,(
    ! [X26,X27,X28] :
      ( ( r1_xboole_0(X26,k2_xboole_0(X27,X28))
        | ~ r1_xboole_0(X26,X27)
        | ~ r1_xboole_0(X26,X28) )
      & ( r1_xboole_0(X26,X27)
        | ~ r1_xboole_0(X26,k2_xboole_0(X27,X28)) )
      & ( r1_xboole_0(X26,X28)
        | ~ r1_xboole_0(X26,k2_xboole_0(X27,X28)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_55,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_45]),c_0_28]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_57,negated_conjecture,
    ( k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) = esk3_0
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_59,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_45]),c_0_28]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_60,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r1_xboole_0(esk3_0,X1)
    | r2_hidden(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43])).

fof(c_0_62,plain,(
    ! [X15,X16] :
      ( ~ r1_xboole_0(X15,X16)
      | r1_xboole_0(X16,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_63,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r1_xboole_0(esk3_0,X1)
    | r1_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

fof(c_0_64,plain,(
    ! [X67,X68] :
      ( ( k4_xboole_0(k1_tarski(X67),k1_tarski(X68)) != k1_tarski(X67)
        | X67 != X68 )
      & ( X67 = X68
        | k4_xboole_0(k1_tarski(X67),k1_tarski(X68)) = k1_tarski(X67) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

fof(c_0_65,plain,(
    ! [X21,X22] : k4_xboole_0(X21,X22) = k5_xboole_0(X21,k3_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_66,plain,(
    ! [X19,X20] :
      ( ( k4_xboole_0(X19,X20) != k1_xboole_0
        | r1_tarski(X19,X20) )
      & ( ~ r1_tarski(X19,X20)
        | k4_xboole_0(X19,X20) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_67,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_68,negated_conjecture,
    ( r1_xboole_0(X1,esk4_0)
    | ~ r1_xboole_0(X1,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_49])).

cnf(c_0_69,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r1_xboole_0(esk3_0,X1)
    | r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_57])).

cnf(c_0_71,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_72,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

fof(c_0_73,plain,(
    ! [X14] : k3_xboole_0(X14,X14) = X14 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_74,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_75,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

fof(c_0_76,plain,(
    ! [X23,X24] :
      ( ~ r1_tarski(X23,X24)
      | k2_xboole_0(X23,X24) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_77,plain,(
    ! [X25] :
      ( ( r1_xboole_0(X25,X25)
        | X25 != k1_xboole_0 )
      & ( X25 = k1_xboole_0
        | ~ r1_xboole_0(X25,X25) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

cnf(c_0_78,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r1_xboole_0(X1,esk4_0)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_57])).

cnf(c_0_79,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r1_xboole_0(X1,esk3_0)
    | r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,k1_tarski(X2))
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_81,plain,
    ( X1 != X2
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_45]),c_0_45]),c_0_45]),c_0_28]),c_0_28]),c_0_28]),c_0_72]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_43])).

cnf(c_0_82,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_83,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_74,c_0_72])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_75])).

cnf(c_0_85,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_86,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_87,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r1_xboole_0(X1,esk4_0)
    | r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_88,negated_conjecture,
    ( esk3_0 != k1_tarski(esk2_0)
    | esk4_0 != k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_89,plain,
    ( r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_45]),c_0_28]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_90,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_81]),c_0_82])).

cnf(c_0_91,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_82])).

fof(c_0_92,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_93,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_94,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | r1_tarski(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_95,negated_conjecture,
    ( esk3_0 != k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)
    | esk4_0 != k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_45]),c_0_45]),c_0_28]),c_0_28]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43])).

cnf(c_0_96,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_97,plain,
    ( r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[c_0_89])).

cnf(c_0_98,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_99,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_100,negated_conjecture,
    ( esk3_0 != k1_tarski(esk2_0)
    | esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_101,negated_conjecture,
    ( k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) = esk4_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_49])).

cnf(c_0_102,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 != esk3_0 ),
    inference(spm,[status(thm)],[c_0_95,c_0_57])).

cnf(c_0_103,plain,
    ( ~ r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98])).

cnf(c_0_104,plain,
    ( r1_tarski(k6_enumset1(esk1_2(X1,X2),esk1_2(X1,X2),esk1_2(X1,X2),esk1_2(X1,X2),esk1_2(X1,X2),esk1_2(X1,X2),esk1_2(X1,X2),esk1_2(X1,X2)),X1)
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_99])).

cnf(c_0_105,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | esk4_0 != k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_106,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    | esk3_0 != k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_45]),c_0_28]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_107,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_101]),c_0_102])).

cnf(c_0_108,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_109,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | esk4_0 != k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_45]),c_0_28]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_110,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_57])).

cnf(c_0_111,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_93,c_0_108])).

cnf(c_0_112,negated_conjecture,
    ( k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_110])])).

cnf(c_0_113,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_110]),c_0_110]),c_0_110]),c_0_110]),c_0_110]),c_0_110]),c_0_110]),c_0_111]),c_0_112]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:01:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.13/0.40  # and selection function GSelectMinInfpos.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.028 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.13/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.40  fof(t43_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 0.13/0.40  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.13/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.40  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.40  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.40  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.13/0.40  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.13/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.40  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.13/0.40  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.13/0.40  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.13/0.40  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.13/0.40  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.13/0.40  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.13/0.40  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.40  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.13/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.40  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.13/0.40  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.13/0.40  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 0.13/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.40  fof(c_0_23, plain, ![X65, X66]:k3_tarski(k2_tarski(X65,X66))=k2_xboole_0(X65,X66), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.13/0.40  fof(c_0_24, plain, ![X32, X33]:k1_enumset1(X32,X32,X33)=k2_tarski(X32,X33), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.40  fof(c_0_25, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0))))), inference(assume_negation,[status(cth)],[t43_zfmisc_1])).
% 0.13/0.40  fof(c_0_26, plain, ![X29, X30]:r1_tarski(X29,k2_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.13/0.40  cnf(c_0_27, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.40  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  fof(c_0_29, plain, ![X34, X35, X36]:k2_enumset1(X34,X34,X35,X36)=k1_enumset1(X34,X35,X36), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.40  fof(c_0_30, plain, ![X37, X38, X39, X40]:k3_enumset1(X37,X37,X38,X39,X40)=k2_enumset1(X37,X38,X39,X40), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.40  fof(c_0_31, plain, ![X41, X42, X43, X44, X45]:k4_enumset1(X41,X41,X42,X43,X44,X45)=k3_enumset1(X41,X42,X43,X44,X45), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.40  fof(c_0_32, plain, ![X46, X47, X48, X49, X50, X51]:k5_enumset1(X46,X46,X47,X48,X49,X50,X51)=k4_enumset1(X46,X47,X48,X49,X50,X51), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.13/0.40  fof(c_0_33, plain, ![X52, X53, X54, X55, X56, X57, X58]:k6_enumset1(X52,X52,X53,X54,X55,X56,X57,X58)=k5_enumset1(X52,X53,X54,X55,X56,X57,X58), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.13/0.40  fof(c_0_34, negated_conjecture, (((k1_tarski(esk2_0)=k2_xboole_0(esk3_0,esk4_0)&(esk3_0!=k1_tarski(esk2_0)|esk4_0!=k1_tarski(esk2_0)))&(esk3_0!=k1_xboole_0|esk4_0!=k1_tarski(esk2_0)))&(esk3_0!=k1_tarski(esk2_0)|esk4_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.13/0.40  fof(c_0_35, plain, ![X31]:k2_tarski(X31,X31)=k1_tarski(X31), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.40  fof(c_0_36, plain, ![X63, X64]:((~r1_tarski(X63,k1_tarski(X64))|(X63=k1_xboole_0|X63=k1_tarski(X64)))&((X63!=k1_xboole_0|r1_tarski(X63,k1_tarski(X64)))&(X63!=k1_tarski(X64)|r1_tarski(X63,k1_tarski(X64))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.13/0.40  cnf(c_0_37, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.40  cnf(c_0_38, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.40  cnf(c_0_39, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.40  cnf(c_0_40, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.40  cnf(c_0_41, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.40  cnf(c_0_42, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.40  cnf(c_0_43, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.40  cnf(c_0_44, negated_conjecture, (k1_tarski(esk2_0)=k2_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.40  cnf(c_0_45, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.40  fof(c_0_46, plain, ![X61, X62]:(r2_hidden(X61,X62)|r1_xboole_0(k1_tarski(X61),X62)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.13/0.40  cnf(c_0_47, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.40  cnf(c_0_48, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43])).
% 0.13/0.40  cnf(c_0_49, negated_conjecture, (k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)=k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45]), c_0_28]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43])).
% 0.13/0.40  fof(c_0_50, plain, ![X59, X60]:((~r1_tarski(k1_tarski(X59),X60)|r2_hidden(X59,X60))&(~r2_hidden(X59,X60)|r1_tarski(k1_tarski(X59),X60))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.13/0.40  cnf(c_0_51, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.40  cnf(c_0_52, plain, (X1=k1_xboole_0|X1=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|~r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_45]), c_0_45]), c_0_28]), c_0_28]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43])).
% 0.13/0.40  cnf(c_0_53, negated_conjecture, (r1_tarski(esk3_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.40  fof(c_0_54, plain, ![X26, X27, X28]:((r1_xboole_0(X26,k2_xboole_0(X27,X28))|~r1_xboole_0(X26,X27)|~r1_xboole_0(X26,X28))&((r1_xboole_0(X26,X27)|~r1_xboole_0(X26,k2_xboole_0(X27,X28)))&(r1_xboole_0(X26,X28)|~r1_xboole_0(X26,k2_xboole_0(X27,X28))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.13/0.40  cnf(c_0_55, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.13/0.40  cnf(c_0_56, plain, (r2_hidden(X1,X2)|r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_45]), c_0_28]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43])).
% 0.13/0.40  cnf(c_0_57, negated_conjecture, (k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)=esk3_0|esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.13/0.40  cnf(c_0_58, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.13/0.40  cnf(c_0_59, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_45]), c_0_28]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43])).
% 0.13/0.40  cnf(c_0_60, negated_conjecture, (esk3_0=k1_xboole_0|r1_xboole_0(esk3_0,X1)|r2_hidden(esk2_0,X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.13/0.40  cnf(c_0_61, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43])).
% 0.13/0.40  fof(c_0_62, plain, ![X15, X16]:(~r1_xboole_0(X15,X16)|r1_xboole_0(X16,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.13/0.40  cnf(c_0_63, negated_conjecture, (esk3_0=k1_xboole_0|r1_xboole_0(esk3_0,X1)|r1_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),X1)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.13/0.40  fof(c_0_64, plain, ![X67, X68]:((k4_xboole_0(k1_tarski(X67),k1_tarski(X68))!=k1_tarski(X67)|X67!=X68)&(X67=X68|k4_xboole_0(k1_tarski(X67),k1_tarski(X68))=k1_tarski(X67))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 0.13/0.40  fof(c_0_65, plain, ![X21, X22]:k4_xboole_0(X21,X22)=k5_xboole_0(X21,k3_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.40  fof(c_0_66, plain, ![X19, X20]:((k4_xboole_0(X19,X20)!=k1_xboole_0|r1_tarski(X19,X20))&(~r1_tarski(X19,X20)|k4_xboole_0(X19,X20)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.13/0.40  fof(c_0_67, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.40  cnf(c_0_68, negated_conjecture, (r1_xboole_0(X1,esk4_0)|~r1_xboole_0(X1,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_61, c_0_49])).
% 0.13/0.40  cnf(c_0_69, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.13/0.40  cnf(c_0_70, negated_conjecture, (esk3_0=k1_xboole_0|r1_xboole_0(esk3_0,X1)|r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_63, c_0_57])).
% 0.13/0.40  cnf(c_0_71, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.13/0.40  cnf(c_0_72, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.13/0.40  fof(c_0_73, plain, ![X14]:k3_xboole_0(X14,X14)=X14, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.13/0.40  cnf(c_0_74, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.13/0.40  cnf(c_0_75, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.13/0.40  fof(c_0_76, plain, ![X23, X24]:(~r1_tarski(X23,X24)|k2_xboole_0(X23,X24)=X24), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.13/0.40  fof(c_0_77, plain, ![X25]:((r1_xboole_0(X25,X25)|X25!=k1_xboole_0)&(X25=k1_xboole_0|~r1_xboole_0(X25,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 0.13/0.40  cnf(c_0_78, negated_conjecture, (esk3_0=k1_xboole_0|r1_xboole_0(X1,esk4_0)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_68, c_0_57])).
% 0.13/0.40  cnf(c_0_79, negated_conjecture, (esk3_0=k1_xboole_0|r1_xboole_0(X1,esk3_0)|r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.13/0.40  cnf(c_0_80, plain, (r1_tarski(X1,k1_tarski(X2))|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.40  cnf(c_0_81, plain, (X1!=X2|k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))!=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_45]), c_0_45]), c_0_45]), c_0_28]), c_0_28]), c_0_28]), c_0_72]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_43])).
% 0.13/0.40  cnf(c_0_82, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.13/0.40  cnf(c_0_83, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_74, c_0_72])).
% 0.13/0.40  cnf(c_0_84, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_75])).
% 0.13/0.40  cnf(c_0_85, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.13/0.40  cnf(c_0_86, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.13/0.40  cnf(c_0_87, negated_conjecture, (esk3_0=k1_xboole_0|r1_xboole_0(X1,esk4_0)|r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.13/0.40  cnf(c_0_88, negated_conjecture, (esk3_0!=k1_tarski(esk2_0)|esk4_0!=k1_tarski(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.40  cnf(c_0_89, plain, (r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))|X1!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_45]), c_0_28]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43])).
% 0.13/0.40  cnf(c_0_90, plain, (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))!=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_81]), c_0_82])).
% 0.13/0.40  cnf(c_0_91, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_82])).
% 0.13/0.40  fof(c_0_92, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.40  cnf(c_0_93, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43])).
% 0.13/0.40  cnf(c_0_94, negated_conjecture, (esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|r1_tarski(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.13/0.40  cnf(c_0_95, negated_conjecture, (esk3_0!=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)|esk4_0!=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_45]), c_0_45]), c_0_28]), c_0_28]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43])).
% 0.13/0.40  cnf(c_0_96, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.13/0.40  cnf(c_0_97, plain, (r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))), inference(er,[status(thm)],[c_0_89])).
% 0.13/0.40  cnf(c_0_98, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_90, c_0_91])).
% 0.13/0.40  cnf(c_0_99, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_92])).
% 0.13/0.40  cnf(c_0_100, negated_conjecture, (esk3_0!=k1_tarski(esk2_0)|esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.40  cnf(c_0_101, negated_conjecture, (k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)=esk4_0|esk4_0=k1_xboole_0|esk3_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_49])).
% 0.13/0.40  cnf(c_0_102, negated_conjecture, (esk3_0=k1_xboole_0|esk4_0!=esk3_0), inference(spm,[status(thm)],[c_0_95, c_0_57])).
% 0.13/0.40  cnf(c_0_103, plain, (~r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_98])).
% 0.13/0.40  cnf(c_0_104, plain, (r1_tarski(k6_enumset1(esk1_2(X1,X2),esk1_2(X1,X2),esk1_2(X1,X2),esk1_2(X1,X2),esk1_2(X1,X2),esk1_2(X1,X2),esk1_2(X1,X2),esk1_2(X1,X2)),X1)|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_59, c_0_99])).
% 0.13/0.40  cnf(c_0_105, negated_conjecture, (esk3_0!=k1_xboole_0|esk4_0!=k1_tarski(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.40  cnf(c_0_106, negated_conjecture, (esk4_0!=k1_xboole_0|esk3_0!=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_45]), c_0_28]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43])).
% 0.13/0.40  cnf(c_0_107, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_101]), c_0_102])).
% 0.13/0.40  cnf(c_0_108, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.13/0.40  cnf(c_0_109, negated_conjecture, (esk3_0!=k1_xboole_0|esk4_0!=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105, c_0_45]), c_0_28]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43])).
% 0.13/0.40  cnf(c_0_110, negated_conjecture, (esk3_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_57])).
% 0.13/0.40  cnf(c_0_111, plain, (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_93, c_0_108])).
% 0.13/0.40  cnf(c_0_112, negated_conjecture, (k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_110])])).
% 0.13/0.40  cnf(c_0_113, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_110]), c_0_110]), c_0_110]), c_0_110]), c_0_110]), c_0_110]), c_0_110]), c_0_111]), c_0_112]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 114
% 0.13/0.40  # Proof object clause steps            : 67
% 0.13/0.40  # Proof object formula steps           : 47
% 0.13/0.40  # Proof object conjectures             : 27
% 0.13/0.40  # Proof object clause conjectures      : 24
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 28
% 0.13/0.40  # Proof object initial formulas used   : 23
% 0.13/0.40  # Proof object generating inferences   : 19
% 0.13/0.40  # Proof object simplifying inferences  : 144
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 23
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 38
% 0.13/0.40  # Removed in clause preprocessing      : 9
% 0.13/0.40  # Initial clauses in saturation        : 29
% 0.13/0.40  # Processed clauses                    : 381
% 0.13/0.40  # ...of these trivial                  : 4
% 0.13/0.40  # ...subsumed                          : 183
% 0.13/0.40  # ...remaining for further processing  : 193
% 0.13/0.40  # Other redundant clauses eliminated   : 6
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 12
% 0.13/0.40  # Backward-rewritten                   : 89
% 0.13/0.40  # Generated clauses                    : 882
% 0.13/0.40  # ...of the previous two non-trivial   : 730
% 0.13/0.40  # Contextual simplify-reflections      : 3
% 0.13/0.40  # Paramodulations                      : 876
% 0.13/0.40  # Factorizations                       : 0
% 0.13/0.40  # Equation resolutions                 : 6
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 59
% 0.13/0.40  #    Positive orientable unit clauses  : 14
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 3
% 0.13/0.40  #    Non-unit-clauses                  : 42
% 0.13/0.40  # Current number of unprocessed clauses: 373
% 0.13/0.40  # ...number of literals in the above   : 1140
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 137
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 1449
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 889
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 193
% 0.13/0.40  # Unit Clause-clause subsumption calls : 79
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 54
% 0.13/0.40  # BW rewrite match successes           : 11
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 16497
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.053 s
% 0.13/0.40  # System time              : 0.002 s
% 0.13/0.40  # Total time               : 0.055 s
% 0.13/0.40  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
