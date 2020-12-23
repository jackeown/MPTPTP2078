%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:49 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  154 (100997 expanded)
%              Number of clauses        :  103 (37930 expanded)
%              Number of leaves         :   25 (31084 expanded)
%              Depth                    :   28
%              Number of atoms          :  275 (127213 expanded)
%              Number of equality atoms :  140 (118873 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t43_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_xboole_0
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(c_0_25,plain,(
    ! [X76,X77] : k3_tarski(k2_tarski(X76,X77)) = k2_xboole_0(X76,X77) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_26,plain,(
    ! [X43,X44] : k1_enumset1(X43,X43,X44) = k2_tarski(X43,X44) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_xboole_0
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t43_zfmisc_1])).

fof(c_0_28,plain,(
    ! [X40,X41] : k3_xboole_0(X40,X41) = k5_xboole_0(k5_xboole_0(X40,X41),k2_xboole_0(X40,X41)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_29,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_31,plain,(
    ! [X45,X46,X47] : k2_enumset1(X45,X45,X46,X47) = k1_enumset1(X45,X46,X47) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_32,plain,(
    ! [X48,X49,X50,X51] : k3_enumset1(X48,X48,X49,X50,X51) = k2_enumset1(X48,X49,X50,X51) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_33,plain,(
    ! [X34,X35] : r1_tarski(X34,k2_xboole_0(X34,X35)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_34,plain,(
    ! [X52,X53,X54,X55,X56] : k4_enumset1(X52,X52,X53,X54,X55,X56) = k3_enumset1(X52,X53,X54,X55,X56) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_35,plain,(
    ! [X57,X58,X59,X60,X61,X62] : k5_enumset1(X57,X57,X58,X59,X60,X61,X62) = k4_enumset1(X57,X58,X59,X60,X61,X62) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_36,plain,(
    ! [X63,X64,X65,X66,X67,X68,X69] : k6_enumset1(X63,X63,X64,X65,X66,X67,X68,X69) = k5_enumset1(X63,X64,X65,X66,X67,X68,X69) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_37,negated_conjecture,
    ( k1_tarski(esk3_0) = k2_xboole_0(esk4_0,esk5_0)
    & ( esk4_0 != k1_tarski(esk3_0)
      | esk5_0 != k1_tarski(esk3_0) )
    & ( esk4_0 != k1_xboole_0
      | esk5_0 != k1_tarski(esk3_0) )
    & ( esk4_0 != k1_tarski(esk3_0)
      | esk5_0 != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

fof(c_0_38,plain,(
    ! [X42] : k2_tarski(X42,X42) = k1_tarski(X42) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_39,plain,(
    ! [X28,X29] : r1_tarski(k3_xboole_0(X28,X29),X28) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_42,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_44,plain,(
    ! [X17] : k3_xboole_0(X17,X17) = X17 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_45,plain,(
    ! [X16] : k2_xboole_0(X16,X16) = X16 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_46,plain,(
    ! [X74,X75] :
      ( ( ~ r1_tarski(X74,k1_tarski(X75))
        | X74 = k1_xboole_0
        | X74 = k1_tarski(X75) )
      & ( X74 != k1_xboole_0
        | r1_tarski(X74,k1_tarski(X75)) )
      & ( X74 != k1_tarski(X75)
        | r1_tarski(X74,k1_tarski(X75)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_48,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_49,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_50,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_51,negated_conjecture,
    ( k1_tarski(esk3_0) = k2_xboole_0(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_52,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_53,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_54,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43])).

fof(c_0_55,plain,(
    ! [X36,X37,X38] : k5_xboole_0(k5_xboole_0(X36,X37),X38) = k5_xboole_0(X36,k5_xboole_0(X37,X38)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_57,plain,(
    ! [X39] : k5_xboole_0(X39,X39) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_59,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_41]),c_0_42]),c_0_43]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_61,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k3_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52]),c_0_30]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_50]),c_0_50])).

cnf(c_0_62,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_63,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_64,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_54]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_65,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_66,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_41]),c_0_42]),c_0_43]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_67,plain,
    ( X1 = k1_xboole_0
    | X1 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_52]),c_0_52]),c_0_30]),c_0_30]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_50]),c_0_50])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_69,plain,
    ( r1_tarski(k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),X1) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

fof(c_0_70,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k5_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_71,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65]),c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( esk4_0 != k1_tarski(esk3_0)
    | esk5_0 != k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_73,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = esk4_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk4_0,k5_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))),esk4_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_61])).

cnf(c_0_75,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_76,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_65]),c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( esk4_0 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | esk5_0 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_52]),c_0_52]),c_0_30]),c_0_30]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_50]),c_0_50])).

fof(c_0_78,plain,(
    ! [X72,X73] :
      ( r2_hidden(X72,X73)
      | r1_xboole_0(k1_tarski(X72),X73) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

fof(c_0_79,plain,(
    ! [X18,X19,X21,X22,X23] :
      ( ( r1_xboole_0(X18,X19)
        | r2_hidden(esk2_2(X18,X19),k3_xboole_0(X18,X19)) )
      & ( ~ r2_hidden(X23,k3_xboole_0(X21,X22))
        | ~ r1_xboole_0(X21,X22) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_80,negated_conjecture,
    ( esk4_0 != k1_tarski(esk3_0)
    | esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_81,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | X1 = esk4_0
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_73])).

cnf(c_0_82,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(esk5_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_73]),c_0_75]),c_0_76])).

cnf(c_0_83,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 != esk4_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_73])).

fof(c_0_84,plain,(
    ! [X31,X32,X33] :
      ( ~ r1_tarski(X31,X32)
      | ~ r1_xboole_0(X32,X33)
      | r1_xboole_0(X31,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_85,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_86,plain,
    ( r1_tarski(X1,k1_tarski(X2))
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_87,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_88,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | esk4_0 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_52]),c_0_30]),c_0_42]),c_0_43]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_89,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83])).

cnf(c_0_90,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_91,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_92,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_52]),c_0_30]),c_0_42]),c_0_43]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_93,plain,
    ( r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_52]),c_0_30]),c_0_42]),c_0_43]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_94,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_54]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_95,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_73])).

cnf(c_0_96,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k5_xboole_0(k5_xboole_0(X2,X3),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_54]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_97,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(X3,X2)
    | ~ r1_tarski(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_98,plain,
    ( r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[c_0_93])).

fof(c_0_99,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk1_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk1_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_100,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) ),
    inference(rw,[status(thm)],[c_0_94,c_0_63])).

cnf(c_0_101,negated_conjecture,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,esk5_0)) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_95]),c_0_95]),c_0_95]),c_0_95]),c_0_95]),c_0_95]),c_0_95])).

cnf(c_0_102,plain,
    ( ~ r1_xboole_0(X1,X2)
    | ~ r2_hidden(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) ),
    inference(rw,[status(thm)],[c_0_96,c_0_63])).

cnf(c_0_103,plain,
    ( r1_xboole_0(k1_xboole_0,X1)
    | r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_104,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_105,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,esk5_0)
    | r2_hidden(esk2_2(k1_xboole_0,esk5_0),k5_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_71])).

cnf(c_0_106,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X3,k5_xboole_0(X2,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X2)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_71])).

cnf(c_0_107,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,esk5_0)
    | r2_hidden(esk2_2(k1_xboole_0,esk5_0),X1)
    | ~ r1_tarski(k5_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_108,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_95]),c_0_71]),c_0_95])).

fof(c_0_109,plain,(
    ! [X24,X25] :
      ( ( r1_tarski(X24,X25)
        | X24 != X25 )
      & ( r1_tarski(X25,X24)
        | X24 != X25 )
      & ( ~ r1_tarski(X24,X25)
        | ~ r1_tarski(X25,X24)
        | X24 = X25 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_110,plain,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_66]),c_0_71])).

cnf(c_0_111,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,esk5_0)
    | r2_hidden(esk2_2(k1_xboole_0,esk5_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_112,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

cnf(c_0_113,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_114,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,esk5_0)
    | r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_115,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = X1
    | ~ r1_tarski(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_112,c_0_60])).

cnf(c_0_116,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,esk5_0)
    | r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_113,c_0_114])).

cnf(c_0_117,negated_conjecture,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = k1_xboole_0
    | r1_xboole_0(k1_xboole_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_115,c_0_116])).

fof(c_0_118,plain,(
    ! [X26,X27] :
      ( ~ r1_tarski(X26,X27)
      | k2_xboole_0(X26,X27) = X27 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_119,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    | esk5_0 != k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_120,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0
    | r1_xboole_0(k1_xboole_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_117])).

cnf(c_0_121,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_118])).

cnf(c_0_122,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_123,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    | esk5_0 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_52]),c_0_30]),c_0_42]),c_0_43]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_124,negated_conjecture,
    ( X1 = k1_xboole_0
    | r1_xboole_0(k1_xboole_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_120]),c_0_116])).

cnf(c_0_125,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_121,c_0_41]),c_0_42]),c_0_43]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_126,plain,
    ( r2_hidden(X1,k1_xboole_0)
    | r1_tarski(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_110,c_0_122])).

cnf(c_0_127,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_123,c_0_95])])).

cnf(c_0_128,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k3_tarski(k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_124])).

cnf(c_0_129,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_125,c_0_69])).

cnf(c_0_130,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_113,c_0_126])).

cnf(c_0_131,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,esk5_0)
    | k3_tarski(k1_xboole_0) != esk5_0 ),
    inference(spm,[status(thm)],[c_0_127,c_0_128])).

cnf(c_0_132,negated_conjecture,
    ( k3_tarski(k1_xboole_0) = X1
    | r1_xboole_0(k1_xboole_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_129,c_0_124])).

cnf(c_0_133,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_115,c_0_130])).

cnf(c_0_134,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,esk5_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_132])])).

cnf(c_0_135,negated_conjecture,
    ( k5_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k5_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_112,c_0_108])).

cnf(c_0_136,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0
    | r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_101,c_0_133])).

fof(c_0_137,plain,(
    ! [X30] : k5_xboole_0(X30,k1_xboole_0) = X30 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_138,negated_conjecture,
    ( ~ r2_hidden(X1,k5_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_134]),c_0_101]),c_0_71])).

cnf(c_0_139,negated_conjecture,
    ( k5_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) = k1_xboole_0
    | k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_135,c_0_136])).

cnf(c_0_140,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_137])).

cnf(c_0_141,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),X1) ),
    inference(spm,[status(thm)],[c_0_138,c_0_122])).

cnf(c_0_142,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_139]),c_0_140]),c_0_127])).

cnf(c_0_143,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_112,c_0_130])).

cnf(c_0_144,negated_conjecture,
    ( r1_tarski(esk5_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_141,c_0_142]),c_0_140])).

cnf(c_0_145,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_127,c_0_142])).

cnf(c_0_146,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = X1
    | ~ r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) ),
    inference(spm,[status(thm)],[c_0_112,c_0_69])).

cnf(c_0_147,negated_conjecture,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,esk5_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_101,c_0_142])).

cnf(c_0_148,negated_conjecture,
    ( r1_tarski(X1,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_144]),c_0_145])).

cnf(c_0_149,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

cnf(c_0_150,negated_conjecture,
    ( ~ r1_tarski(k1_xboole_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_147]),c_0_140]),c_0_71]),c_0_140]),c_0_71]),c_0_145])).

cnf(c_0_151,negated_conjecture,
    ( X1 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_142]),c_0_148])])).

cnf(c_0_152,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_149])).

cnf(c_0_153,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_150,c_0_151]),c_0_152])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:46:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.43  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.19/0.43  # and selection function GSelectMinInfpos.
% 0.19/0.43  #
% 0.19/0.43  # Preprocessing time       : 0.028 s
% 0.19/0.43  # Presaturation interreduction done
% 0.19/0.43  
% 0.19/0.43  # Proof found!
% 0.19/0.43  # SZS status Theorem
% 0.19/0.43  # SZS output start CNFRefutation
% 0.19/0.43  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.43  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.43  fof(t43_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 0.19/0.43  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.19/0.43  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.43  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.43  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.43  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.43  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.43  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.19/0.43  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.43  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.19/0.43  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.19/0.43  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.19/0.43  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.19/0.43  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.19/0.43  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.19/0.43  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.19/0.43  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.19/0.43  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.43  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.19/0.43  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.43  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.43  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.43  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.19/0.43  fof(c_0_25, plain, ![X76, X77]:k3_tarski(k2_tarski(X76,X77))=k2_xboole_0(X76,X77), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.43  fof(c_0_26, plain, ![X43, X44]:k1_enumset1(X43,X43,X44)=k2_tarski(X43,X44), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.43  fof(c_0_27, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0))))), inference(assume_negation,[status(cth)],[t43_zfmisc_1])).
% 0.19/0.43  fof(c_0_28, plain, ![X40, X41]:k3_xboole_0(X40,X41)=k5_xboole_0(k5_xboole_0(X40,X41),k2_xboole_0(X40,X41)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.19/0.43  cnf(c_0_29, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.43  cnf(c_0_30, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.43  fof(c_0_31, plain, ![X45, X46, X47]:k2_enumset1(X45,X45,X46,X47)=k1_enumset1(X45,X46,X47), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.43  fof(c_0_32, plain, ![X48, X49, X50, X51]:k3_enumset1(X48,X48,X49,X50,X51)=k2_enumset1(X48,X49,X50,X51), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.43  fof(c_0_33, plain, ![X34, X35]:r1_tarski(X34,k2_xboole_0(X34,X35)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.43  fof(c_0_34, plain, ![X52, X53, X54, X55, X56]:k4_enumset1(X52,X52,X53,X54,X55,X56)=k3_enumset1(X52,X53,X54,X55,X56), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.43  fof(c_0_35, plain, ![X57, X58, X59, X60, X61, X62]:k5_enumset1(X57,X57,X58,X59,X60,X61,X62)=k4_enumset1(X57,X58,X59,X60,X61,X62), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.43  fof(c_0_36, plain, ![X63, X64, X65, X66, X67, X68, X69]:k6_enumset1(X63,X63,X64,X65,X66,X67,X68,X69)=k5_enumset1(X63,X64,X65,X66,X67,X68,X69), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.19/0.43  fof(c_0_37, negated_conjecture, (((k1_tarski(esk3_0)=k2_xboole_0(esk4_0,esk5_0)&(esk4_0!=k1_tarski(esk3_0)|esk5_0!=k1_tarski(esk3_0)))&(esk4_0!=k1_xboole_0|esk5_0!=k1_tarski(esk3_0)))&(esk4_0!=k1_tarski(esk3_0)|esk5_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).
% 0.19/0.43  fof(c_0_38, plain, ![X42]:k2_tarski(X42,X42)=k1_tarski(X42), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.43  fof(c_0_39, plain, ![X28, X29]:r1_tarski(k3_xboole_0(X28,X29),X28), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.19/0.43  cnf(c_0_40, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.43  cnf(c_0_41, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.43  cnf(c_0_42, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.43  cnf(c_0_43, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.43  fof(c_0_44, plain, ![X17]:k3_xboole_0(X17,X17)=X17, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.19/0.43  fof(c_0_45, plain, ![X16]:k2_xboole_0(X16,X16)=X16, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.19/0.43  fof(c_0_46, plain, ![X74, X75]:((~r1_tarski(X74,k1_tarski(X75))|(X74=k1_xboole_0|X74=k1_tarski(X75)))&((X74!=k1_xboole_0|r1_tarski(X74,k1_tarski(X75)))&(X74!=k1_tarski(X75)|r1_tarski(X74,k1_tarski(X75))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.19/0.43  cnf(c_0_47, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.43  cnf(c_0_48, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.43  cnf(c_0_49, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.43  cnf(c_0_50, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.43  cnf(c_0_51, negated_conjecture, (k1_tarski(esk3_0)=k2_xboole_0(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.43  cnf(c_0_52, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.43  cnf(c_0_53, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.43  cnf(c_0_54, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_43])).
% 0.19/0.43  fof(c_0_55, plain, ![X36, X37, X38]:k5_xboole_0(k5_xboole_0(X36,X37),X38)=k5_xboole_0(X36,k5_xboole_0(X37,X38)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.19/0.43  cnf(c_0_56, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.43  fof(c_0_57, plain, ![X39]:k5_xboole_0(X39,X39)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.19/0.43  cnf(c_0_58, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.43  cnf(c_0_59, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.43  cnf(c_0_60, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_41]), c_0_42]), c_0_43]), c_0_48]), c_0_49]), c_0_50])).
% 0.19/0.43  cnf(c_0_61, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k3_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52]), c_0_30]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_50]), c_0_50])).
% 0.19/0.43  cnf(c_0_62, plain, (r1_tarski(k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54]), c_0_48]), c_0_49]), c_0_50])).
% 0.19/0.43  cnf(c_0_63, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.43  cnf(c_0_64, plain, (k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_54]), c_0_48]), c_0_49]), c_0_50])).
% 0.19/0.43  cnf(c_0_65, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.43  cnf(c_0_66, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_41]), c_0_42]), c_0_43]), c_0_48]), c_0_49]), c_0_50])).
% 0.19/0.43  cnf(c_0_67, plain, (X1=k1_xboole_0|X1=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|~r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_52]), c_0_52]), c_0_30]), c_0_30]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_50]), c_0_50])).
% 0.19/0.43  cnf(c_0_68, negated_conjecture, (r1_tarski(esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.43  cnf(c_0_69, plain, (r1_tarski(k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),X1)), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.43  fof(c_0_70, plain, ![X8, X9]:k5_xboole_0(X8,X9)=k5_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.19/0.43  cnf(c_0_71, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65]), c_0_66])).
% 0.19/0.43  cnf(c_0_72, negated_conjecture, (esk4_0!=k1_tarski(esk3_0)|esk5_0!=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.43  cnf(c_0_73, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=esk4_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.19/0.43  cnf(c_0_74, negated_conjecture, (r1_tarski(k5_xboole_0(esk4_0,k5_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))),esk4_0)), inference(spm,[status(thm)],[c_0_69, c_0_61])).
% 0.19/0.43  cnf(c_0_75, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.19/0.43  cnf(c_0_76, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_65]), c_0_71])).
% 0.19/0.43  cnf(c_0_77, negated_conjecture, (esk4_0!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|esk5_0!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_52]), c_0_52]), c_0_30]), c_0_30]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_50]), c_0_50])).
% 0.19/0.43  fof(c_0_78, plain, ![X72, X73]:(r2_hidden(X72,X73)|r1_xboole_0(k1_tarski(X72),X73)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.19/0.43  fof(c_0_79, plain, ![X18, X19, X21, X22, X23]:((r1_xboole_0(X18,X19)|r2_hidden(esk2_2(X18,X19),k3_xboole_0(X18,X19)))&(~r2_hidden(X23,k3_xboole_0(X21,X22))|~r1_xboole_0(X21,X22))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.43  cnf(c_0_80, negated_conjecture, (esk4_0!=k1_tarski(esk3_0)|esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.43  cnf(c_0_81, negated_conjecture, (esk4_0=k1_xboole_0|X1=k1_xboole_0|X1=esk4_0|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_67, c_0_73])).
% 0.19/0.43  cnf(c_0_82, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(esk5_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_73]), c_0_75]), c_0_76])).
% 0.19/0.43  cnf(c_0_83, negated_conjecture, (esk4_0=k1_xboole_0|esk5_0!=esk4_0), inference(spm,[status(thm)],[c_0_77, c_0_73])).
% 0.19/0.43  fof(c_0_84, plain, ![X31, X32, X33]:(~r1_tarski(X31,X32)|~r1_xboole_0(X32,X33)|r1_xboole_0(X31,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.19/0.43  cnf(c_0_85, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.19/0.43  cnf(c_0_86, plain, (r1_tarski(X1,k1_tarski(X2))|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.43  cnf(c_0_87, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.19/0.43  cnf(c_0_88, negated_conjecture, (esk5_0!=k1_xboole_0|esk4_0!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_52]), c_0_30]), c_0_42]), c_0_43]), c_0_48]), c_0_49]), c_0_50])).
% 0.19/0.43  cnf(c_0_89, negated_conjecture, (esk5_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_83])).
% 0.19/0.43  cnf(c_0_90, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.19/0.43  cnf(c_0_91, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.19/0.43  cnf(c_0_92, plain, (r2_hidden(X1,X2)|r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_52]), c_0_30]), c_0_42]), c_0_43]), c_0_48]), c_0_49]), c_0_50])).
% 0.19/0.43  cnf(c_0_93, plain, (r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))|X1!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_52]), c_0_30]), c_0_42]), c_0_43]), c_0_48]), c_0_49]), c_0_50])).
% 0.19/0.43  cnf(c_0_94, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_54]), c_0_48]), c_0_49]), c_0_50])).
% 0.19/0.43  cnf(c_0_95, negated_conjecture, (esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_73])).
% 0.19/0.43  cnf(c_0_96, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k5_xboole_0(k5_xboole_0(X2,X3),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_54]), c_0_48]), c_0_49]), c_0_50])).
% 0.19/0.43  cnf(c_0_97, plain, (r1_xboole_0(X1,X2)|r2_hidden(X3,X2)|~r1_tarski(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.19/0.43  cnf(c_0_98, plain, (r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))), inference(er,[status(thm)],[c_0_93])).
% 0.19/0.43  fof(c_0_99, plain, ![X10, X11, X12, X13, X14]:((~r1_tarski(X10,X11)|(~r2_hidden(X12,X10)|r2_hidden(X12,X11)))&((r2_hidden(esk1_2(X13,X14),X13)|r1_tarski(X13,X14))&(~r2_hidden(esk1_2(X13,X14),X14)|r1_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.43  cnf(c_0_100, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))))), inference(rw,[status(thm)],[c_0_94, c_0_63])).
% 0.19/0.43  cnf(c_0_101, negated_conjecture, (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,esk5_0))=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_95]), c_0_95]), c_0_95]), c_0_95]), c_0_95]), c_0_95]), c_0_95])).
% 0.19/0.43  cnf(c_0_102, plain, (~r1_xboole_0(X1,X2)|~r2_hidden(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))))), inference(rw,[status(thm)],[c_0_96, c_0_63])).
% 0.19/0.43  cnf(c_0_103, plain, (r1_xboole_0(k1_xboole_0,X1)|r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.19/0.43  cnf(c_0_104, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_99])).
% 0.19/0.43  cnf(c_0_105, negated_conjecture, (r1_xboole_0(k1_xboole_0,esk5_0)|r2_hidden(esk2_2(k1_xboole_0,esk5_0),k5_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_71])).
% 0.19/0.43  cnf(c_0_106, plain, (r2_hidden(X1,X2)|~r2_hidden(X3,k5_xboole_0(X2,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X2))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_71])).
% 0.19/0.43  cnf(c_0_107, negated_conjecture, (r1_xboole_0(k1_xboole_0,esk5_0)|r2_hidden(esk2_2(k1_xboole_0,esk5_0),X1)|~r1_tarski(k5_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),X1)), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 0.19/0.43  cnf(c_0_108, negated_conjecture, (r1_tarski(k5_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_95]), c_0_71]), c_0_95])).
% 0.19/0.43  fof(c_0_109, plain, ![X24, X25]:(((r1_tarski(X24,X25)|X24!=X25)&(r1_tarski(X25,X24)|X24!=X25))&(~r1_tarski(X24,X25)|~r1_tarski(X25,X24)|X24=X25)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.43  cnf(c_0_110, plain, (r2_hidden(X1,k1_xboole_0)|~r2_hidden(X2,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_66]), c_0_71])).
% 0.19/0.43  cnf(c_0_111, negated_conjecture, (r1_xboole_0(k1_xboole_0,esk5_0)|r2_hidden(esk2_2(k1_xboole_0,esk5_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_107, c_0_108])).
% 0.19/0.43  cnf(c_0_112, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_109])).
% 0.19/0.43  cnf(c_0_113, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_99])).
% 0.19/0.43  cnf(c_0_114, negated_conjecture, (r1_xboole_0(k1_xboole_0,esk5_0)|r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_110, c_0_111])).
% 0.19/0.43  cnf(c_0_115, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=X1|~r1_tarski(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X1)), inference(spm,[status(thm)],[c_0_112, c_0_60])).
% 0.19/0.43  cnf(c_0_116, negated_conjecture, (r1_xboole_0(k1_xboole_0,esk5_0)|r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_113, c_0_114])).
% 0.19/0.43  cnf(c_0_117, negated_conjecture, (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=k1_xboole_0|r1_xboole_0(k1_xboole_0,esk5_0)), inference(spm,[status(thm)],[c_0_115, c_0_116])).
% 0.19/0.43  fof(c_0_118, plain, ![X26, X27]:(~r1_tarski(X26,X27)|k2_xboole_0(X26,X27)=X27), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.43  cnf(c_0_119, negated_conjecture, (esk4_0!=k1_xboole_0|esk5_0!=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.43  cnf(c_0_120, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0|r1_xboole_0(k1_xboole_0,esk5_0)), inference(spm,[status(thm)],[c_0_101, c_0_117])).
% 0.19/0.43  cnf(c_0_121, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_118])).
% 0.19/0.43  cnf(c_0_122, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_99])).
% 0.19/0.43  cnf(c_0_123, negated_conjecture, (esk4_0!=k1_xboole_0|esk5_0!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119, c_0_52]), c_0_30]), c_0_42]), c_0_43]), c_0_48]), c_0_49]), c_0_50])).
% 0.19/0.43  cnf(c_0_124, negated_conjecture, (X1=k1_xboole_0|r1_xboole_0(k1_xboole_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_120]), c_0_116])).
% 0.19/0.43  cnf(c_0_125, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_121, c_0_41]), c_0_42]), c_0_43]), c_0_48]), c_0_49]), c_0_50])).
% 0.19/0.43  cnf(c_0_126, plain, (r2_hidden(X1,k1_xboole_0)|r1_tarski(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_110, c_0_122])).
% 0.19/0.43  cnf(c_0_127, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_123, c_0_95])])).
% 0.19/0.43  cnf(c_0_128, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k3_tarski(k1_xboole_0)|r1_xboole_0(k1_xboole_0,esk5_0)), inference(spm,[status(thm)],[c_0_101, c_0_124])).
% 0.19/0.43  cnf(c_0_129, plain, (k3_tarski(k6_enumset1(k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),X1))=X1), inference(spm,[status(thm)],[c_0_125, c_0_69])).
% 0.19/0.43  cnf(c_0_130, plain, (r1_tarski(k1_xboole_0,X1)|r1_tarski(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_113, c_0_126])).
% 0.19/0.43  cnf(c_0_131, negated_conjecture, (r1_xboole_0(k1_xboole_0,esk5_0)|k3_tarski(k1_xboole_0)!=esk5_0), inference(spm,[status(thm)],[c_0_127, c_0_128])).
% 0.19/0.43  cnf(c_0_132, negated_conjecture, (k3_tarski(k1_xboole_0)=X1|r1_xboole_0(k1_xboole_0,esk5_0)), inference(spm,[status(thm)],[c_0_129, c_0_124])).
% 0.19/0.43  cnf(c_0_133, plain, (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=k1_xboole_0|r1_tarski(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_115, c_0_130])).
% 0.19/0.43  cnf(c_0_134, negated_conjecture, (r1_xboole_0(k1_xboole_0,esk5_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_132])])).
% 0.19/0.43  cnf(c_0_135, negated_conjecture, (k5_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))=k1_xboole_0|~r1_tarski(k1_xboole_0,k5_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))), inference(spm,[status(thm)],[c_0_112, c_0_108])).
% 0.19/0.43  cnf(c_0_136, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0|r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_101, c_0_133])).
% 0.19/0.43  fof(c_0_137, plain, ![X30]:k5_xboole_0(X30,k1_xboole_0)=X30, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.19/0.43  cnf(c_0_138, negated_conjecture, (~r2_hidden(X1,k5_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_134]), c_0_101]), c_0_71])).
% 0.19/0.43  cnf(c_0_139, negated_conjecture, (k5_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))=k1_xboole_0|k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_135, c_0_136])).
% 0.19/0.43  cnf(c_0_140, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_137])).
% 0.19/0.43  cnf(c_0_141, negated_conjecture, (r1_tarski(k5_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),X1)), inference(spm,[status(thm)],[c_0_138, c_0_122])).
% 0.19/0.43  cnf(c_0_142, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_139]), c_0_140]), c_0_127])).
% 0.19/0.43  cnf(c_0_143, plain, (X1=k1_xboole_0|r1_tarski(X2,k1_xboole_0)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_112, c_0_130])).
% 0.19/0.43  cnf(c_0_144, negated_conjecture, (r1_tarski(esk5_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_141, c_0_142]), c_0_140])).
% 0.19/0.43  cnf(c_0_145, negated_conjecture, (esk5_0!=k1_xboole_0), inference(rw,[status(thm)],[c_0_127, c_0_142])).
% 0.19/0.43  cnf(c_0_146, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))=X1|~r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))))), inference(spm,[status(thm)],[c_0_112, c_0_69])).
% 0.19/0.43  cnf(c_0_147, negated_conjecture, (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,esk5_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_101, c_0_142])).
% 0.19/0.43  cnf(c_0_148, negated_conjecture, (r1_tarski(X1,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_144]), c_0_145])).
% 0.19/0.43  cnf(c_0_149, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_109])).
% 0.19/0.43  cnf(c_0_150, negated_conjecture, (~r1_tarski(k1_xboole_0,esk5_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146, c_0_147]), c_0_140]), c_0_71]), c_0_140]), c_0_71]), c_0_145])).
% 0.19/0.43  cnf(c_0_151, negated_conjecture, (X1=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_142]), c_0_148])])).
% 0.19/0.43  cnf(c_0_152, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_149])).
% 0.19/0.43  cnf(c_0_153, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_150, c_0_151]), c_0_152])]), ['proof']).
% 0.19/0.43  # SZS output end CNFRefutation
% 0.19/0.43  # Proof object total steps             : 154
% 0.19/0.43  # Proof object clause steps            : 103
% 0.19/0.43  # Proof object formula steps           : 51
% 0.19/0.43  # Proof object conjectures             : 47
% 0.19/0.43  # Proof object clause conjectures      : 44
% 0.19/0.43  # Proof object formula conjectures     : 3
% 0.19/0.43  # Proof object initial clauses used    : 33
% 0.19/0.43  # Proof object initial formulas used   : 25
% 0.19/0.43  # Proof object generating inferences   : 41
% 0.19/0.43  # Proof object simplifying inferences  : 155
% 0.19/0.43  # Training examples: 0 positive, 0 negative
% 0.19/0.43  # Parsed axioms                        : 26
% 0.19/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.43  # Initial clauses                      : 37
% 0.19/0.43  # Removed in clause preprocessing      : 9
% 0.19/0.43  # Initial clauses in saturation        : 28
% 0.19/0.43  # Processed clauses                    : 480
% 0.19/0.43  # ...of these trivial                  : 14
% 0.19/0.43  # ...subsumed                          : 216
% 0.19/0.43  # ...remaining for further processing  : 250
% 0.19/0.43  # Other redundant clauses eliminated   : 8
% 0.19/0.43  # Clauses deleted for lack of memory   : 0
% 0.19/0.43  # Backward-subsumed                    : 29
% 0.19/0.43  # Backward-rewritten                   : 181
% 0.19/0.43  # Generated clauses                    : 2692
% 0.19/0.43  # ...of the previous two non-trivial   : 2350
% 0.19/0.43  # Contextual simplify-reflections      : 5
% 0.19/0.43  # Paramodulations                      : 2679
% 0.19/0.43  # Factorizations                       : 5
% 0.19/0.43  # Equation resolutions                 : 8
% 0.19/0.43  # Propositional unsat checks           : 0
% 0.19/0.43  #    Propositional check models        : 0
% 0.19/0.43  #    Propositional check unsatisfiable : 0
% 0.19/0.43  #    Propositional clauses             : 0
% 0.19/0.43  #    Propositional clauses after purity: 0
% 0.19/0.43  #    Propositional unsat core size     : 0
% 0.19/0.43  #    Propositional preprocessing time  : 0.000
% 0.19/0.43  #    Propositional encoding time       : 0.000
% 0.19/0.43  #    Propositional solver time         : 0.000
% 0.19/0.43  #    Success case prop preproc time    : 0.000
% 0.19/0.43  #    Success case prop encoding time   : 0.000
% 0.19/0.43  #    Success case prop solver time     : 0.000
% 0.19/0.43  # Current number of processed clauses  : 10
% 0.19/0.43  #    Positive orientable unit clauses  : 3
% 0.19/0.43  #    Positive unorientable unit clauses: 1
% 0.19/0.43  #    Negative unit clauses             : 0
% 0.19/0.43  #    Non-unit-clauses                  : 6
% 0.19/0.43  # Current number of unprocessed clauses: 1599
% 0.19/0.43  # ...number of literals in the above   : 4557
% 0.19/0.43  # Current number of archived formulas  : 0
% 0.19/0.43  # Current number of archived clauses   : 245
% 0.19/0.43  # Clause-clause subsumption calls (NU) : 1649
% 0.19/0.43  # Rec. Clause-clause subsumption calls : 1055
% 0.19/0.43  # Non-unit clause-clause subsumptions  : 206
% 0.19/0.43  # Unit Clause-clause subsumption calls : 60
% 0.19/0.43  # Rewrite failures with RHS unbound    : 5
% 0.19/0.43  # BW rewrite match attempts            : 190
% 0.19/0.43  # BW rewrite match successes           : 149
% 0.19/0.43  # Condensation attempts                : 0
% 0.19/0.43  # Condensation successes               : 0
% 0.19/0.43  # Termbank termtop insertions          : 41324
% 0.19/0.43  
% 0.19/0.43  # -------------------------------------------------
% 0.19/0.43  # User time                : 0.092 s
% 0.19/0.43  # System time              : 0.005 s
% 0.19/0.43  # Total time               : 0.097 s
% 0.19/0.43  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
