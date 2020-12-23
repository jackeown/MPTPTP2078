%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:48 EST 2020

% Result     : Theorem 0.55s
% Output     : CNFRefutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  132 (2947 expanded)
%              Number of clauses        :   77 (1112 expanded)
%              Number of leaves         :   27 ( 906 expanded)
%              Depth                    :   16
%              Number of atoms          :  237 (3641 expanded)
%              Number of equality atoms :  139 (3339 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    7 (   2 average)
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

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t61_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

fof(t67_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_27,plain,(
    ! [X92,X93] : k3_tarski(k2_tarski(X92,X93)) = k2_xboole_0(X92,X93) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_28,plain,(
    ! [X59,X60] : k1_enumset1(X59,X59,X60) = k2_tarski(X59,X60) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_xboole_0
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t43_zfmisc_1])).

fof(c_0_30,plain,(
    ! [X41,X42] : k3_xboole_0(X41,X42) = k5_xboole_0(k5_xboole_0(X41,X42),k2_xboole_0(X41,X42)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_31,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_33,plain,(
    ! [X61,X62,X63] : k2_enumset1(X61,X61,X62,X63) = k1_enumset1(X61,X62,X63) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_34,plain,(
    ! [X64,X65,X66,X67] : k3_enumset1(X64,X64,X65,X66,X67) = k2_enumset1(X64,X65,X66,X67) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_35,plain,(
    ! [X88,X89] :
      ( r2_hidden(X88,X89)
      | r1_xboole_0(k1_tarski(X88),X89) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

fof(c_0_36,plain,(
    ! [X58] : k2_tarski(X58,X58) = k1_tarski(X58) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_37,plain,(
    ! [X68,X69,X70,X71,X72] : k4_enumset1(X68,X68,X69,X70,X71,X72) = k3_enumset1(X68,X69,X70,X71,X72) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_38,plain,(
    ! [X73,X74,X75,X76,X77,X78] : k5_enumset1(X73,X73,X74,X75,X76,X77,X78) = k4_enumset1(X73,X74,X75,X76,X77,X78) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_39,plain,(
    ! [X79,X80,X81,X82,X83,X84,X85] : k6_enumset1(X79,X79,X80,X81,X82,X83,X84,X85) = k5_enumset1(X79,X80,X81,X82,X83,X84,X85) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_40,plain,(
    ! [X35,X36] : r1_tarski(X35,k2_xboole_0(X35,X36)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_41,negated_conjecture,
    ( k1_tarski(esk3_0) = k2_xboole_0(esk4_0,esk5_0)
    & ( esk4_0 != k1_tarski(esk3_0)
      | esk5_0 != k1_tarski(esk3_0) )
    & ( esk4_0 != k1_xboole_0
      | esk5_0 != k1_tarski(esk3_0) )
    & ( esk4_0 != k1_tarski(esk3_0)
      | esk5_0 != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

fof(c_0_42,plain,(
    ! [X17,X18] :
      ( ( ~ r1_xboole_0(X17,X18)
        | k3_xboole_0(X17,X18) = k1_xboole_0 )
      & ( k3_xboole_0(X17,X18) != k1_xboole_0
        | r1_xboole_0(X17,X18) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_45,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_47,plain,(
    ! [X32,X33,X34] :
      ( ~ r1_tarski(X32,X33)
      | ~ r1_xboole_0(X33,X34)
      | r1_xboole_0(X32,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_49,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_50,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_54,negated_conjecture,
    ( k1_tarski(esk3_0) = k2_xboole_0(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46])).

fof(c_0_57,plain,(
    ! [X37,X38,X39] : k5_xboole_0(k5_xboole_0(X37,X38),X39) = k5_xboole_0(X37,k5_xboole_0(X38,X39)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_58,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_32]),c_0_45]),c_0_46]),c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_44]),c_0_45]),c_0_46]),c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k3_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_49]),c_0_32]),c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_52]),c_0_52])).

fof(c_0_62,plain,(
    ! [X20] : k3_xboole_0(X20,X20) = X20 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_63,plain,(
    ! [X19] : k2_xboole_0(X19,X19) = X19 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_64,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56]),c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_65,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_66,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(X3,X2)
    | ~ r1_tarski(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

fof(c_0_68,plain,(
    ! [X90,X91] :
      ( ( ~ r1_tarski(X90,k1_tarski(X91))
        | X90 = k1_xboole_0
        | X90 = k1_tarski(X91) )
      & ( X90 != k1_xboole_0
        | r1_tarski(X90,k1_tarski(X91)) )
      & ( X90 != k1_tarski(X91)
        | r1_tarski(X90,k1_tarski(X91)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_69,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

fof(c_0_70,plain,(
    ! [X40] : k5_xboole_0(X40,X40) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_71,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( r1_xboole_0(esk4_0,X1)
    | r2_hidden(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_74,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_75,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_56]),c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_76,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_77,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_44]),c_0_45]),c_0_46]),c_0_50]),c_0_51]),c_0_52])).

fof(c_0_78,plain,(
    ! [X21,X22,X24,X25,X26] :
      ( ( r1_xboole_0(X21,X22)
        | r2_hidden(esk2_2(X21,X22),k3_xboole_0(X21,X22)) )
      & ( ~ r2_hidden(X26,k3_xboole_0(X24,X25))
        | ~ r1_xboole_0(X24,X25) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_79,plain,(
    ! [X86,X87] :
      ( ( ~ r1_tarski(k1_tarski(X86),X87)
        | r2_hidden(X86,X87) )
      & ( ~ r2_hidden(X86,X87)
        | r1_tarski(k1_tarski(X86),X87) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_80,negated_conjecture,
    ( k5_xboole_0(esk4_0,k5_xboole_0(X1,k3_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1)))) = k1_xboole_0
    | r2_hidden(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_81,plain,
    ( X1 = k1_xboole_0
    | X1 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_49]),c_0_49]),c_0_32]),c_0_32]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_52]),c_0_52])).

fof(c_0_82,plain,(
    ! [X9,X10] : k5_xboole_0(X9,X10) = k5_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_83,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76]),c_0_77])).

cnf(c_0_84,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

fof(c_0_85,plain,(
    ! [X43,X44,X45,X46,X47,X48,X49] : k5_enumset1(X43,X44,X45,X46,X47,X48,X49) = k2_xboole_0(k4_enumset1(X43,X44,X45,X46,X47,X48),k1_tarski(X49)) ),
    inference(variable_rename,[status(thm)],[t61_enumset1])).

fof(c_0_86,plain,(
    ! [X50,X51,X52,X53,X54,X55,X56,X57] : k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57) = k2_xboole_0(k4_enumset1(X50,X51,X52,X53,X54,X55),k2_tarski(X56,X57)) ),
    inference(variable_rename,[status(thm)],[t67_enumset1])).

cnf(c_0_87,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_88,negated_conjecture,
    ( k5_xboole_0(esk4_0,k5_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) = k1_xboole_0
    | r2_hidden(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_61])).

cnf(c_0_89,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = esk4_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_81,c_0_67])).

cnf(c_0_90,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_91,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_76]),c_0_83])).

cnf(c_0_92,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k5_xboole_0(k5_xboole_0(X2,X3),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_56]),c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_93,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_94,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

fof(c_0_95,plain,(
    ! [X29,X30] :
      ( ~ r1_tarski(X29,X30)
      | k2_xboole_0(X29,X30) = X30 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_96,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_49]),c_0_32]),c_0_45]),c_0_46]),c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_97,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | r2_hidden(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90]),c_0_91])).

cnf(c_0_98,plain,
    ( ~ r1_xboole_0(X1,X2)
    | ~ r2_hidden(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) ),
    inference(rw,[status(thm)],[c_0_92,c_0_65])).

cnf(c_0_99,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_49]),c_0_32]),c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52])).

cnf(c_0_100,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_32]),c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52])).

fof(c_0_101,plain,(
    ! [X31] : k5_xboole_0(X31,k1_xboole_0) = X31 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_102,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_103,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_104,negated_conjecture,
    ( esk4_0 != k1_tarski(esk3_0)
    | esk5_0 != k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_105,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | ~ r2_hidden(X2,k5_xboole_0(esk4_0,k5_xboole_0(X1,k3_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1))))) ),
    inference(spm,[status(thm)],[c_0_98,c_0_73])).

cnf(c_0_106,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X7) = k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_107,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

fof(c_0_108,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk1_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk1_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_109,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_110,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_44]),c_0_45]),c_0_46]),c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_111,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | r1_tarski(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_89])).

cnf(c_0_112,negated_conjecture,
    ( esk4_0 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | esk5_0 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_49]),c_0_49]),c_0_32]),c_0_32]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_52]),c_0_52])).

cnf(c_0_113,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_77]),c_0_76]),c_0_107])).

cnf(c_0_114,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

cnf(c_0_115,plain,
    ( r1_xboole_0(X1,X2)
    | k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_56]),c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_116,negated_conjecture,
    ( esk4_0 != k1_tarski(esk3_0)
    | esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_117,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = esk5_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_61])).

cnf(c_0_118,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 != esk4_0 ),
    inference(spm,[status(thm)],[c_0_112,c_0_89])).

cnf(c_0_119,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_113,c_0_114])).

cnf(c_0_120,plain,
    ( r1_xboole_0(X1,X2)
    | k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_115,c_0_65])).

cnf(c_0_121,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    | esk5_0 != k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_122,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | esk4_0 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_49]),c_0_32]),c_0_45]),c_0_46]),c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_123,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_117]),c_0_118])).

cnf(c_0_124,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1)) = X1
    | r2_hidden(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_110,c_0_119])).

cnf(c_0_125,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_106]),c_0_77]),c_0_76]),c_0_107])])).

cnf(c_0_126,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    | esk5_0 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_121,c_0_49]),c_0_32]),c_0_45]),c_0_46]),c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_127,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_89])).

cnf(c_0_128,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = esk5_0
    | r2_hidden(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_124])).

cnf(c_0_129,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_125]),c_0_77]),c_0_83]),c_0_83])).

cnf(c_0_130,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_126,c_0_127])])).

cnf(c_0_131,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_128,c_0_127]),c_0_129]),c_0_130]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:55:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.55/0.72  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.55/0.72  # and selection function GSelectMinInfpos.
% 0.55/0.72  #
% 0.55/0.72  # Preprocessing time       : 0.028 s
% 0.55/0.72  # Presaturation interreduction done
% 0.55/0.72  
% 0.55/0.72  # Proof found!
% 0.55/0.72  # SZS status Theorem
% 0.55/0.72  # SZS output start CNFRefutation
% 0.55/0.72  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.55/0.72  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.55/0.72  fof(t43_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 0.55/0.72  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.55/0.72  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.55/0.72  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.55/0.72  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.55/0.72  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.55/0.72  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.55/0.72  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.55/0.72  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.55/0.72  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.55/0.72  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.55/0.72  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.55/0.72  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.55/0.72  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.55/0.72  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.55/0.72  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.55/0.72  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.55/0.72  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.55/0.72  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.55/0.72  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.55/0.72  fof(t61_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_enumset1)).
% 0.55/0.72  fof(t67_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_enumset1)).
% 0.55/0.72  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.55/0.72  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.55/0.72  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.55/0.72  fof(c_0_27, plain, ![X92, X93]:k3_tarski(k2_tarski(X92,X93))=k2_xboole_0(X92,X93), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.55/0.72  fof(c_0_28, plain, ![X59, X60]:k1_enumset1(X59,X59,X60)=k2_tarski(X59,X60), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.55/0.72  fof(c_0_29, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0))))), inference(assume_negation,[status(cth)],[t43_zfmisc_1])).
% 0.55/0.72  fof(c_0_30, plain, ![X41, X42]:k3_xboole_0(X41,X42)=k5_xboole_0(k5_xboole_0(X41,X42),k2_xboole_0(X41,X42)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.55/0.72  cnf(c_0_31, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.55/0.72  cnf(c_0_32, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.55/0.72  fof(c_0_33, plain, ![X61, X62, X63]:k2_enumset1(X61,X61,X62,X63)=k1_enumset1(X61,X62,X63), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.55/0.72  fof(c_0_34, plain, ![X64, X65, X66, X67]:k3_enumset1(X64,X64,X65,X66,X67)=k2_enumset1(X64,X65,X66,X67), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.55/0.72  fof(c_0_35, plain, ![X88, X89]:(r2_hidden(X88,X89)|r1_xboole_0(k1_tarski(X88),X89)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.55/0.72  fof(c_0_36, plain, ![X58]:k2_tarski(X58,X58)=k1_tarski(X58), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.55/0.72  fof(c_0_37, plain, ![X68, X69, X70, X71, X72]:k4_enumset1(X68,X68,X69,X70,X71,X72)=k3_enumset1(X68,X69,X70,X71,X72), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.55/0.72  fof(c_0_38, plain, ![X73, X74, X75, X76, X77, X78]:k5_enumset1(X73,X73,X74,X75,X76,X77,X78)=k4_enumset1(X73,X74,X75,X76,X77,X78), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.55/0.72  fof(c_0_39, plain, ![X79, X80, X81, X82, X83, X84, X85]:k6_enumset1(X79,X79,X80,X81,X82,X83,X84,X85)=k5_enumset1(X79,X80,X81,X82,X83,X84,X85), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.55/0.72  fof(c_0_40, plain, ![X35, X36]:r1_tarski(X35,k2_xboole_0(X35,X36)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.55/0.72  fof(c_0_41, negated_conjecture, (((k1_tarski(esk3_0)=k2_xboole_0(esk4_0,esk5_0)&(esk4_0!=k1_tarski(esk3_0)|esk5_0!=k1_tarski(esk3_0)))&(esk4_0!=k1_xboole_0|esk5_0!=k1_tarski(esk3_0)))&(esk4_0!=k1_tarski(esk3_0)|esk5_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).
% 0.55/0.72  fof(c_0_42, plain, ![X17, X18]:((~r1_xboole_0(X17,X18)|k3_xboole_0(X17,X18)=k1_xboole_0)&(k3_xboole_0(X17,X18)!=k1_xboole_0|r1_xboole_0(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.55/0.72  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.55/0.72  cnf(c_0_44, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.55/0.72  cnf(c_0_45, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.55/0.72  cnf(c_0_46, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.55/0.72  fof(c_0_47, plain, ![X32, X33, X34]:(~r1_tarski(X32,X33)|~r1_xboole_0(X33,X34)|r1_xboole_0(X32,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.55/0.72  cnf(c_0_48, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.55/0.72  cnf(c_0_49, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.55/0.72  cnf(c_0_50, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.55/0.72  cnf(c_0_51, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.55/0.72  cnf(c_0_52, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.55/0.72  cnf(c_0_53, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.55/0.72  cnf(c_0_54, negated_conjecture, (k1_tarski(esk3_0)=k2_xboole_0(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.55/0.72  cnf(c_0_55, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.55/0.72  cnf(c_0_56, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46])).
% 0.55/0.72  fof(c_0_57, plain, ![X37, X38, X39]:k5_xboole_0(k5_xboole_0(X37,X38),X39)=k5_xboole_0(X37,k5_xboole_0(X38,X39)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.55/0.72  cnf(c_0_58, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.55/0.72  cnf(c_0_59, plain, (r2_hidden(X1,X2)|r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49]), c_0_32]), c_0_45]), c_0_46]), c_0_50]), c_0_51]), c_0_52])).
% 0.55/0.72  cnf(c_0_60, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_44]), c_0_45]), c_0_46]), c_0_50]), c_0_51]), c_0_52])).
% 0.55/0.72  cnf(c_0_61, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k3_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_49]), c_0_32]), c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_52]), c_0_52])).
% 0.55/0.72  fof(c_0_62, plain, ![X20]:k3_xboole_0(X20,X20)=X20, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.55/0.72  fof(c_0_63, plain, ![X19]:k2_xboole_0(X19,X19)=X19, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.55/0.72  cnf(c_0_64, plain, (k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56]), c_0_50]), c_0_51]), c_0_52])).
% 0.55/0.72  cnf(c_0_65, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.55/0.72  cnf(c_0_66, plain, (r1_xboole_0(X1,X2)|r2_hidden(X3,X2)|~r1_tarski(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.55/0.72  cnf(c_0_67, negated_conjecture, (r1_tarski(esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.55/0.72  fof(c_0_68, plain, ![X90, X91]:((~r1_tarski(X90,k1_tarski(X91))|(X90=k1_xboole_0|X90=k1_tarski(X91)))&((X90!=k1_xboole_0|r1_tarski(X90,k1_tarski(X91)))&(X90!=k1_tarski(X91)|r1_tarski(X90,k1_tarski(X91))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.55/0.72  cnf(c_0_69, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.55/0.72  fof(c_0_70, plain, ![X40]:k5_xboole_0(X40,X40)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.55/0.72  cnf(c_0_71, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.55/0.72  cnf(c_0_72, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_64, c_0_65])).
% 0.55/0.72  cnf(c_0_73, negated_conjecture, (r1_xboole_0(esk4_0,X1)|r2_hidden(esk3_0,X1)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.55/0.72  cnf(c_0_74, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.55/0.72  cnf(c_0_75, plain, (k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_56]), c_0_50]), c_0_51]), c_0_52])).
% 0.55/0.72  cnf(c_0_76, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.55/0.72  cnf(c_0_77, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_44]), c_0_45]), c_0_46]), c_0_50]), c_0_51]), c_0_52])).
% 0.55/0.72  fof(c_0_78, plain, ![X21, X22, X24, X25, X26]:((r1_xboole_0(X21,X22)|r2_hidden(esk2_2(X21,X22),k3_xboole_0(X21,X22)))&(~r2_hidden(X26,k3_xboole_0(X24,X25))|~r1_xboole_0(X24,X25))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.55/0.72  fof(c_0_79, plain, ![X86, X87]:((~r1_tarski(k1_tarski(X86),X87)|r2_hidden(X86,X87))&(~r2_hidden(X86,X87)|r1_tarski(k1_tarski(X86),X87))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.55/0.72  cnf(c_0_80, negated_conjecture, (k5_xboole_0(esk4_0,k5_xboole_0(X1,k3_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1))))=k1_xboole_0|r2_hidden(esk3_0,X1)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.55/0.72  cnf(c_0_81, plain, (X1=k1_xboole_0|X1=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|~r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_49]), c_0_49]), c_0_32]), c_0_32]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_52]), c_0_52])).
% 0.55/0.72  fof(c_0_82, plain, ![X9, X10]:k5_xboole_0(X9,X10)=k5_xboole_0(X10,X9), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.55/0.72  cnf(c_0_83, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76]), c_0_77])).
% 0.55/0.72  cnf(c_0_84, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.55/0.72  fof(c_0_85, plain, ![X43, X44, X45, X46, X47, X48, X49]:k5_enumset1(X43,X44,X45,X46,X47,X48,X49)=k2_xboole_0(k4_enumset1(X43,X44,X45,X46,X47,X48),k1_tarski(X49)), inference(variable_rename,[status(thm)],[t61_enumset1])).
% 0.55/0.72  fof(c_0_86, plain, ![X50, X51, X52, X53, X54, X55, X56, X57]:k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)=k2_xboole_0(k4_enumset1(X50,X51,X52,X53,X54,X55),k2_tarski(X56,X57)), inference(variable_rename,[status(thm)],[t67_enumset1])).
% 0.55/0.72  cnf(c_0_87, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.55/0.72  cnf(c_0_88, negated_conjecture, (k5_xboole_0(esk4_0,k5_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))=k1_xboole_0|r2_hidden(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_80, c_0_61])).
% 0.55/0.72  cnf(c_0_89, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=esk4_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_81, c_0_67])).
% 0.55/0.72  cnf(c_0_90, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.55/0.72  cnf(c_0_91, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_76]), c_0_83])).
% 0.55/0.72  cnf(c_0_92, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k5_xboole_0(k5_xboole_0(X2,X3),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_56]), c_0_50]), c_0_51]), c_0_52])).
% 0.55/0.72  cnf(c_0_93, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7))), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.55/0.72  cnf(c_0_94, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.55/0.72  fof(c_0_95, plain, ![X29, X30]:(~r1_tarski(X29,X30)|k2_xboole_0(X29,X30)=X30), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.55/0.72  cnf(c_0_96, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_49]), c_0_32]), c_0_45]), c_0_46]), c_0_50]), c_0_51]), c_0_52])).
% 0.55/0.72  cnf(c_0_97, negated_conjecture, (esk4_0=k1_xboole_0|esk5_0=k1_xboole_0|r2_hidden(esk3_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_90]), c_0_91])).
% 0.55/0.72  cnf(c_0_98, plain, (~r1_xboole_0(X1,X2)|~r2_hidden(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))))), inference(rw,[status(thm)],[c_0_92, c_0_65])).
% 0.55/0.72  cnf(c_0_99, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_49]), c_0_32]), c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52])).
% 0.55/0.72  cnf(c_0_100, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_32]), c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52])).
% 0.55/0.72  fof(c_0_101, plain, ![X31]:k5_xboole_0(X31,k1_xboole_0)=X31, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.55/0.72  cnf(c_0_102, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_95])).
% 0.55/0.72  cnf(c_0_103, negated_conjecture, (esk5_0=k1_xboole_0|esk4_0=k1_xboole_0|r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk5_0)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.55/0.72  cnf(c_0_104, negated_conjecture, (esk4_0!=k1_tarski(esk3_0)|esk5_0!=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.55/0.72  cnf(c_0_105, negated_conjecture, (r2_hidden(esk3_0,X1)|~r2_hidden(X2,k5_xboole_0(esk4_0,k5_xboole_0(X1,k3_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1)))))), inference(spm,[status(thm)],[c_0_98, c_0_73])).
% 0.55/0.72  cnf(c_0_106, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X7)=k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[c_0_99, c_0_100])).
% 0.55/0.72  cnf(c_0_107, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_101])).
% 0.55/0.72  fof(c_0_108, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk1_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk1_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.55/0.72  cnf(c_0_109, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.55/0.72  cnf(c_0_110, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_44]), c_0_45]), c_0_46]), c_0_50]), c_0_51]), c_0_52])).
% 0.55/0.72  cnf(c_0_111, negated_conjecture, (esk4_0=k1_xboole_0|esk5_0=k1_xboole_0|r1_tarski(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_103, c_0_89])).
% 0.55/0.72  cnf(c_0_112, negated_conjecture, (esk4_0!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|esk5_0!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_49]), c_0_49]), c_0_32]), c_0_32]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_52]), c_0_52])).
% 0.55/0.72  cnf(c_0_113, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|~r2_hidden(X1,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_77]), c_0_76]), c_0_107])).
% 0.55/0.72  cnf(c_0_114, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_108])).
% 0.55/0.72  cnf(c_0_115, plain, (r1_xboole_0(X1,X2)|k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_56]), c_0_50]), c_0_51]), c_0_52])).
% 0.55/0.72  cnf(c_0_116, negated_conjecture, (esk4_0!=k1_tarski(esk3_0)|esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.55/0.72  cnf(c_0_117, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=esk5_0|esk5_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_61])).
% 0.55/0.72  cnf(c_0_118, negated_conjecture, (esk4_0=k1_xboole_0|esk5_0!=esk4_0), inference(spm,[status(thm)],[c_0_112, c_0_89])).
% 0.55/0.72  cnf(c_0_119, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_113, c_0_114])).
% 0.55/0.72  cnf(c_0_120, plain, (r1_xboole_0(X1,X2)|k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_115, c_0_65])).
% 0.55/0.72  cnf(c_0_121, negated_conjecture, (esk4_0!=k1_xboole_0|esk5_0!=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.55/0.72  cnf(c_0_122, negated_conjecture, (esk5_0!=k1_xboole_0|esk4_0!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116, c_0_49]), c_0_32]), c_0_45]), c_0_46]), c_0_50]), c_0_51]), c_0_52])).
% 0.55/0.72  cnf(c_0_123, negated_conjecture, (esk5_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_117]), c_0_118])).
% 0.55/0.72  cnf(c_0_124, negated_conjecture, (k3_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1))=X1|r2_hidden(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_110, c_0_119])).
% 0.55/0.72  cnf(c_0_125, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_106]), c_0_77]), c_0_76]), c_0_107])])).
% 0.55/0.72  cnf(c_0_126, negated_conjecture, (esk4_0!=k1_xboole_0|esk5_0!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_121, c_0_49]), c_0_32]), c_0_45]), c_0_46]), c_0_50]), c_0_51]), c_0_52])).
% 0.55/0.72  cnf(c_0_127, negated_conjecture, (esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_123]), c_0_89])).
% 0.55/0.72  cnf(c_0_128, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=esk5_0|r2_hidden(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_61, c_0_124])).
% 0.55/0.72  cnf(c_0_129, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_125]), c_0_77]), c_0_83]), c_0_83])).
% 0.55/0.72  cnf(c_0_130, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_126, c_0_127])])).
% 0.55/0.72  cnf(c_0_131, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_128, c_0_127]), c_0_129]), c_0_130]), ['proof']).
% 0.55/0.72  # SZS output end CNFRefutation
% 0.55/0.72  # Proof object total steps             : 132
% 0.55/0.72  # Proof object clause steps            : 77
% 0.55/0.72  # Proof object formula steps           : 55
% 0.55/0.72  # Proof object conjectures             : 30
% 0.55/0.72  # Proof object clause conjectures      : 27
% 0.55/0.72  # Proof object formula conjectures     : 3
% 0.55/0.72  # Proof object initial clauses used    : 31
% 0.55/0.72  # Proof object initial formulas used   : 27
% 0.55/0.72  # Proof object generating inferences   : 21
% 0.55/0.72  # Proof object simplifying inferences  : 182
% 0.55/0.72  # Training examples: 0 positive, 0 negative
% 0.55/0.72  # Parsed axioms                        : 28
% 0.55/0.72  # Removed by relevancy pruning/SinE    : 0
% 0.55/0.72  # Initial clauses                      : 40
% 0.55/0.72  # Removed in clause preprocessing      : 9
% 0.55/0.72  # Initial clauses in saturation        : 31
% 0.55/0.72  # Processed clauses                    : 4561
% 0.55/0.72  # ...of these trivial                  : 103
% 0.55/0.72  # ...subsumed                          : 3913
% 0.55/0.72  # ...remaining for further processing  : 544
% 0.55/0.72  # Other redundant clauses eliminated   : 52
% 0.55/0.72  # Clauses deleted for lack of memory   : 0
% 0.55/0.72  # Backward-subsumed                    : 80
% 0.55/0.72  # Backward-rewritten                   : 240
% 0.55/0.72  # Generated clauses                    : 18114
% 0.55/0.72  # ...of the previous two non-trivial   : 14515
% 0.55/0.72  # Contextual simplify-reflections      : 3
% 0.55/0.72  # Paramodulations                      : 18060
% 0.55/0.72  # Factorizations                       : 2
% 0.55/0.72  # Equation resolutions                 : 52
% 0.55/0.72  # Propositional unsat checks           : 0
% 0.55/0.72  #    Propositional check models        : 0
% 0.55/0.72  #    Propositional check unsatisfiable : 0
% 0.55/0.72  #    Propositional clauses             : 0
% 0.55/0.72  #    Propositional clauses after purity: 0
% 0.55/0.72  #    Propositional unsat core size     : 0
% 0.55/0.72  #    Propositional preprocessing time  : 0.000
% 0.55/0.72  #    Propositional encoding time       : 0.000
% 0.55/0.72  #    Propositional solver time         : 0.000
% 0.55/0.72  #    Success case prop preproc time    : 0.000
% 0.55/0.72  #    Success case prop encoding time   : 0.000
% 0.55/0.72  #    Success case prop solver time     : 0.000
% 0.55/0.72  # Current number of processed clauses  : 191
% 0.55/0.72  #    Positive orientable unit clauses  : 96
% 0.55/0.72  #    Positive unorientable unit clauses: 11
% 0.55/0.72  #    Negative unit clauses             : 4
% 0.55/0.72  #    Non-unit-clauses                  : 80
% 0.55/0.72  # Current number of unprocessed clauses: 9359
% 0.55/0.72  # ...number of literals in the above   : 20834
% 0.55/0.72  # Current number of archived formulas  : 0
% 0.55/0.72  # Current number of archived clauses   : 358
% 0.55/0.72  # Clause-clause subsumption calls (NU) : 35611
% 0.55/0.72  # Rec. Clause-clause subsumption calls : 33180
% 0.55/0.72  # Non-unit clause-clause subsumptions  : 3841
% 0.55/0.72  # Unit Clause-clause subsumption calls : 792
% 0.55/0.72  # Rewrite failures with RHS unbound    : 0
% 0.55/0.72  # BW rewrite match attempts            : 3238
% 0.55/0.72  # BW rewrite match successes           : 569
% 0.55/0.72  # Condensation attempts                : 0
% 0.55/0.72  # Condensation successes               : 0
% 0.55/0.72  # Termbank termtop insertions          : 308910
% 0.55/0.72  
% 0.55/0.72  # -------------------------------------------------
% 0.55/0.72  # User time                : 0.368 s
% 0.55/0.72  # System time              : 0.009 s
% 0.55/0.72  # Total time               : 0.377 s
% 0.55/0.72  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
