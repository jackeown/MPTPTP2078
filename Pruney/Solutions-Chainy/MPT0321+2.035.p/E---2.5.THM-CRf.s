%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:02 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :  154 (8961 expanded)
%              Number of clauses        :   99 (3681 expanded)
%              Number of leaves         :   27 (2609 expanded)
%              Depth                    :   25
%              Number of atoms          :  325 (12234 expanded)
%              Number of equality atoms :  122 (9380 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t134_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t6_xboole_0,axiom,(
    ! [X1,X2] :
      ~ ( r2_xboole_0(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ~ r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

fof(t118_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(t117_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))
          | r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) )
        & ~ r1_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_27,plain,(
    ! [X78,X79] : k3_tarski(k2_tarski(X78,X79)) = k2_xboole_0(X78,X79) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_28,plain,(
    ! [X51,X52] : k1_enumset1(X51,X51,X52) = k2_tarski(X51,X52) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_29,plain,(
    ! [X47,X48] : k3_xboole_0(X47,X48) = k5_xboole_0(k5_xboole_0(X47,X48),k2_xboole_0(X47,X48)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_30,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_32,plain,(
    ! [X53,X54,X55] : k2_enumset1(X53,X53,X54,X55) = k1_enumset1(X53,X54,X55) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_33,plain,(
    ! [X56,X57,X58,X59] : k3_enumset1(X56,X56,X57,X58,X59) = k2_enumset1(X56,X57,X58,X59) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_34,plain,(
    ! [X26] : k3_xboole_0(X26,X26) = X26 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_39,plain,(
    ! [X60,X61,X62,X63,X64] : k4_enumset1(X60,X60,X61,X62,X63,X64) = k3_enumset1(X60,X61,X62,X63,X64) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_40,plain,(
    ! [X65,X66,X67,X68,X69,X70] : k5_enumset1(X65,X65,X66,X67,X68,X69,X70) = k4_enumset1(X65,X66,X67,X68,X69,X70) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_41,plain,(
    ! [X71,X72,X73,X74,X75,X76,X77] : k6_enumset1(X71,X71,X72,X73,X74,X75,X76,X77) = k5_enumset1(X71,X72,X73,X74,X75,X76,X77) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_42,plain,(
    ! [X25] : k2_xboole_0(X25,X25) = X25 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_43,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21] :
      ( ( r2_hidden(X17,X14)
        | ~ r2_hidden(X17,X16)
        | X16 != k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X17,X15)
        | ~ r2_hidden(X17,X16)
        | X16 != k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X18,X14)
        | r2_hidden(X18,X15)
        | r2_hidden(X18,X16)
        | X16 != k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk2_3(X19,X20,X21),X21)
        | ~ r2_hidden(esk2_3(X19,X20,X21),X19)
        | r2_hidden(esk2_3(X19,X20,X21),X20)
        | X21 = k4_xboole_0(X19,X20) )
      & ( r2_hidden(esk2_3(X19,X20,X21),X19)
        | r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k4_xboole_0(X19,X20) )
      & ( ~ r2_hidden(esk2_3(X19,X20,X21),X20)
        | r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k4_xboole_0(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_44,plain,(
    ! [X38,X39] : k4_xboole_0(X38,X39) = k5_xboole_0(X38,k3_xboole_0(X38,X39)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_47,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_50,plain,(
    ! [X46] : k5_xboole_0(X46,X46) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_51,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_52,plain,(
    ! [X49,X50] : k2_xboole_0(X49,X50) = k5_xboole_0(X49,k4_xboole_0(X50,X49)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_55,plain,(
    ! [X43,X44,X45] : k5_xboole_0(k5_xboole_0(X43,X44),X45) = k5_xboole_0(X43,k5_xboole_0(X44,X45)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_56,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_36]),c_0_37]),c_0_38]),c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_59,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X4),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X4))))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54]),c_0_46]),c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_61,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_62,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

fof(c_0_63,plain,(
    ! [X27,X28,X30,X31,X32] :
      ( ( r2_hidden(esk3_2(X27,X28),X27)
        | r1_xboole_0(X27,X28) )
      & ( r2_hidden(esk3_2(X27,X28),X28)
        | r1_xboole_0(X27,X28) )
      & ( ~ r2_hidden(X32,X30)
        | ~ r2_hidden(X32,X31)
        | ~ r1_xboole_0(X30,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_64,plain,(
    ! [X42] : r1_xboole_0(X42,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_65,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_66,plain,(
    ! [X40] : k2_xboole_0(X40,k1_xboole_0) = X40 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_67,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_36]),c_0_54]),c_0_37]),c_0_38]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_49]),c_0_49])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))))) ),
    inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61])])).

cnf(c_0_69,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_57]),c_0_62])).

cnf(c_0_70,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_71,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_72,plain,
    ( X3 = k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_54]),c_0_46]),c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_73,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_74,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))))) ),
    inference(rw,[status(thm)],[c_0_67,c_0_61])).

cnf(c_0_75,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))) ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_77,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_78,plain,
    ( X1 = k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))))
    | r2_hidden(esk2_3(X2,X3,X1),X2)
    | r2_hidden(esk2_3(X2,X3,X1),X1) ),
    inference(rw,[status(thm)],[c_0_72,c_0_61])).

cnf(c_0_79,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_36]),c_0_37]),c_0_38]),c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_80,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_69]),c_0_69])).

cnf(c_0_81,plain,
    ( X3 != k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X4,X2),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_54]),c_0_46]),c_0_47]),c_0_48]),c_0_49])).

fof(c_0_82,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | ( X1 = X3
            & X2 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t134_zfmisc_1])).

fof(c_0_83,plain,(
    ! [X80,X81,X82,X83] :
      ( ( r2_hidden(X80,X82)
        | ~ r2_hidden(k4_tarski(X80,X81),k2_zfmisc_1(X82,X83)) )
      & ( r2_hidden(X81,X83)
        | ~ r2_hidden(k4_tarski(X80,X81),k2_zfmisc_1(X82,X83)) )
      & ( ~ r2_hidden(X80,X82)
        | ~ r2_hidden(X81,X83)
        | r2_hidden(k4_tarski(X80,X81),k2_zfmisc_1(X82,X83)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_84,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_58]),c_0_57]),c_0_77])).

cnf(c_0_85,plain,
    ( X1 = k5_xboole_0(X2,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)))
    | r2_hidden(esk2_3(X3,X2,X1),X1)
    | r2_hidden(esk2_3(X3,X2,X1),X3) ),
    inference(rw,[status(thm)],[c_0_78,c_0_69])).

cnf(c_0_86,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_87,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_61])])).

fof(c_0_88,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = k2_zfmisc_1(esk7_0,esk8_0)
    & esk5_0 != k1_xboole_0
    & esk6_0 != k1_xboole_0
    & ( esk5_0 != esk7_0
      | esk6_0 != esk8_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_82])])])).

cnf(c_0_89,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_90,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86]),c_0_57])).

fof(c_0_91,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_92,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_87,c_0_69])).

cnf(c_0_93,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_94,plain,(
    ! [X23,X24] :
      ( ( r1_tarski(X23,X24)
        | ~ r2_xboole_0(X23,X24) )
      & ( X23 != X24
        | ~ r2_xboole_0(X23,X24) )
      & ( ~ r1_tarski(X23,X24)
        | X23 = X24
        | r2_xboole_0(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

fof(c_0_95,plain,(
    ! [X41] : r1_tarski(k1_xboole_0,X41) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_96,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_97,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = k2_zfmisc_1(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_98,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k4_tarski(X2,esk2_3(k1_xboole_0,X3,X1)),k2_zfmisc_1(X4,X1))
    | ~ r2_hidden(X2,X4) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_99,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_100,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk3_2(X1,X2),k5_xboole_0(X2,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)))) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

fof(c_0_101,plain,(
    ! [X33,X34] :
      ( ( r2_hidden(esk4_2(X33,X34),X34)
        | ~ r2_xboole_0(X33,X34) )
      & ( ~ r2_hidden(esk4_2(X33,X34),X33)
        | ~ r2_xboole_0(X33,X34) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_xboole_0])])])])])).

cnf(c_0_102,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_103,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_104,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_105,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k4_tarski(esk1_2(X2,X3),esk2_3(k1_xboole_0,X4,X1)),k2_zfmisc_1(X2,X1))
    | r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_106,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_107,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_3(X3,X2,X4),X3)
    | r2_hidden(esk2_3(X3,X2,X4),X4)
    | ~ r2_hidden(esk3_2(X1,X2),X4) ),
    inference(spm,[status(thm)],[c_0_100,c_0_85])).

cnf(c_0_108,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_109,plain,
    ( k1_xboole_0 = X1
    | r2_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

fof(c_0_110,plain,(
    ! [X87,X88,X89] :
      ( ( r1_tarski(k2_zfmisc_1(X87,X89),k2_zfmisc_1(X88,X89))
        | ~ r1_tarski(X87,X88) )
      & ( r1_tarski(k2_zfmisc_1(X89,X87),k2_zfmisc_1(X89,X88))
        | ~ r1_tarski(X87,X88) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).

cnf(c_0_111,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_112,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,X1),esk7_0)
    | r1_tarski(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_106])).

cnf(c_0_113,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_3(X3,X2,X2),X2)
    | r2_hidden(esk2_3(X3,X2,X2),X3) ),
    inference(spm,[status(thm)],[c_0_107,c_0_93])).

cnf(c_0_114,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_115,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk4_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_116,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_110])).

cnf(c_0_117,negated_conjecture,
    ( r1_tarski(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_111,c_0_112])).

cnf(c_0_118,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_3(X2,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_113])).

cnf(c_0_119,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_97])).

cnf(c_0_120,plain,
    ( k1_xboole_0 = X1
    | X2 = k1_xboole_0
    | r2_hidden(k4_tarski(esk4_2(k1_xboole_0,X1),esk2_3(k1_xboole_0,X3,X2)),k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_98,c_0_115])).

cnf(c_0_121,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

fof(c_0_122,plain,(
    ! [X84,X85,X86] :
      ( ( ~ r1_tarski(k2_zfmisc_1(X85,X84),k2_zfmisc_1(X86,X84))
        | X84 = k1_xboole_0
        | r1_tarski(X85,X86) )
      & ( ~ r1_tarski(k2_zfmisc_1(X84,X85),k2_zfmisc_1(X84,X86))
        | X84 = k1_xboole_0
        | r1_tarski(X85,X86) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).

cnf(c_0_123,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk5_0,X1),k2_zfmisc_1(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_124,plain,
    ( r2_hidden(esk2_3(X1,X1,X1),X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_70,c_0_118])).

cnf(c_0_125,negated_conjecture,
    ( r2_hidden(esk2_3(k1_xboole_0,X1,esk6_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_121]),c_0_106])).

cnf(c_0_126,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_122])).

cnf(c_0_127,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk5_0,esk8_0),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_123,c_0_97])).

cnf(c_0_128,negated_conjecture,
    ( r2_hidden(esk2_3(esk8_0,esk8_0,esk8_0),esk8_0)
    | ~ r2_hidden(esk2_3(k1_xboole_0,X1,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_124,c_0_125])).

cnf(c_0_129,negated_conjecture,
    ( r1_tarski(esk8_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_121])).

cnf(c_0_130,negated_conjecture,
    ( r2_hidden(esk2_3(esk8_0,esk8_0,esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_128,c_0_125])).

cnf(c_0_131,negated_conjecture,
    ( esk8_0 = esk6_0
    | r2_xboole_0(esk8_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_129])).

cnf(c_0_132,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_3(esk8_0,esk8_0,esk8_0)),k2_zfmisc_1(X2,esk8_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_89,c_0_130])).

cnf(c_0_133,negated_conjecture,
    ( r2_hidden(esk4_2(k1_xboole_0,esk5_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_120]),c_0_121]),c_0_106])).

cnf(c_0_134,negated_conjecture,
    ( esk8_0 = esk6_0
    | r2_hidden(esk4_2(esk8_0,esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_131])).

cnf(c_0_135,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_2(k1_xboole_0,esk5_0),esk2_3(esk8_0,esk8_0,esk8_0)),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_133]),c_0_97])).

cnf(c_0_136,negated_conjecture,
    ( esk8_0 = esk6_0
    | r2_hidden(k4_tarski(X1,esk4_2(esk8_0,esk6_0)),k2_zfmisc_1(X2,esk6_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_89,c_0_134])).

cnf(c_0_137,negated_conjecture,
    ( r2_hidden(esk4_2(k1_xboole_0,esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_135])).

cnf(c_0_138,plain,
    ( ~ r2_hidden(esk4_2(X1,X2),X1)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_139,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_122])).

cnf(c_0_140,negated_conjecture,
    ( esk8_0 = esk6_0
    | r2_hidden(k4_tarski(esk4_2(k1_xboole_0,esk5_0),esk4_2(esk8_0,esk6_0)),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_136,c_0_137])).

cnf(c_0_141,negated_conjecture,
    ( esk8_0 = esk6_0
    | ~ r2_hidden(esk4_2(esk8_0,esk6_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_138,c_0_131])).

fof(c_0_142,plain,(
    ! [X36,X37] :
      ( ( r1_tarski(X36,X37)
        | X36 != X37 )
      & ( r1_tarski(X37,X36)
        | X36 != X37 )
      & ( ~ r1_tarski(X36,X37)
        | ~ r1_tarski(X37,X36)
        | X36 = X37 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_143,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r1_tarski(esk7_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(X1,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_139,c_0_97])).

cnf(c_0_144,negated_conjecture,
    ( esk8_0 = esk6_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_140]),c_0_141])).

cnf(c_0_145,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_142])).

cnf(c_0_146,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_142])).

cnf(c_0_147,negated_conjecture,
    ( r1_tarski(esk7_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(X1,esk6_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_143,c_0_144]),c_0_144]),c_0_106])).

cnf(c_0_148,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_145])).

cnf(c_0_149,negated_conjecture,
    ( esk5_0 != esk7_0
    | esk6_0 != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_150,negated_conjecture,
    ( esk7_0 = esk5_0
    | ~ r1_tarski(esk7_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_146,c_0_117])).

cnf(c_0_151,negated_conjecture,
    ( r1_tarski(esk7_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_147,c_0_148])).

cnf(c_0_152,negated_conjecture,
    ( esk7_0 != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_149,c_0_144])])).

cnf(c_0_153,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_150,c_0_151])]),c_0_152]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:09:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 2.55/2.75  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 2.55/2.75  # and selection function GSelectMinInfpos.
% 2.55/2.75  #
% 2.55/2.75  # Preprocessing time       : 0.029 s
% 2.55/2.75  # Presaturation interreduction done
% 2.55/2.75  
% 2.55/2.75  # Proof found!
% 2.55/2.75  # SZS status Theorem
% 2.55/2.75  # SZS output start CNFRefutation
% 2.55/2.75  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.55/2.75  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.55/2.75  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 2.55/2.75  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.55/2.75  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.55/2.75  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.55/2.75  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.55/2.75  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.55/2.75  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 2.55/2.75  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.55/2.75  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.55/2.75  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.55/2.75  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.55/2.75  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.55/2.75  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 2.55/2.75  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.55/2.75  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.55/2.75  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.55/2.75  fof(t134_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 2.55/2.75  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.55/2.75  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.55/2.75  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.55/2.75  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.55/2.75  fof(t6_xboole_0, axiom, ![X1, X2]:~((r2_xboole_0(X1,X2)&![X3]:~((r2_hidden(X3,X2)&~(r2_hidden(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 2.55/2.75  fof(t118_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>(r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 2.55/2.75  fof(t117_zfmisc_1, axiom, ![X1, X2, X3]:~(((X1!=k1_xboole_0&(r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))|r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))))&~(r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 2.55/2.75  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.55/2.75  fof(c_0_27, plain, ![X78, X79]:k3_tarski(k2_tarski(X78,X79))=k2_xboole_0(X78,X79), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 2.55/2.75  fof(c_0_28, plain, ![X51, X52]:k1_enumset1(X51,X51,X52)=k2_tarski(X51,X52), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 2.55/2.75  fof(c_0_29, plain, ![X47, X48]:k3_xboole_0(X47,X48)=k5_xboole_0(k5_xboole_0(X47,X48),k2_xboole_0(X47,X48)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 2.55/2.75  cnf(c_0_30, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 2.55/2.75  cnf(c_0_31, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.55/2.75  fof(c_0_32, plain, ![X53, X54, X55]:k2_enumset1(X53,X53,X54,X55)=k1_enumset1(X53,X54,X55), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 2.55/2.75  fof(c_0_33, plain, ![X56, X57, X58, X59]:k3_enumset1(X56,X56,X57,X58,X59)=k2_enumset1(X56,X57,X58,X59), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 2.55/2.75  fof(c_0_34, plain, ![X26]:k3_xboole_0(X26,X26)=X26, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 2.55/2.75  cnf(c_0_35, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.55/2.75  cnf(c_0_36, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 2.55/2.75  cnf(c_0_37, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 2.55/2.75  cnf(c_0_38, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 2.55/2.75  fof(c_0_39, plain, ![X60, X61, X62, X63, X64]:k4_enumset1(X60,X60,X61,X62,X63,X64)=k3_enumset1(X60,X61,X62,X63,X64), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 2.55/2.75  fof(c_0_40, plain, ![X65, X66, X67, X68, X69, X70]:k5_enumset1(X65,X65,X66,X67,X68,X69,X70)=k4_enumset1(X65,X66,X67,X68,X69,X70), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 2.55/2.75  fof(c_0_41, plain, ![X71, X72, X73, X74, X75, X76, X77]:k6_enumset1(X71,X71,X72,X73,X74,X75,X76,X77)=k5_enumset1(X71,X72,X73,X74,X75,X76,X77), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 2.55/2.75  fof(c_0_42, plain, ![X25]:k2_xboole_0(X25,X25)=X25, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 2.55/2.75  fof(c_0_43, plain, ![X14, X15, X16, X17, X18, X19, X20, X21]:((((r2_hidden(X17,X14)|~r2_hidden(X17,X16)|X16!=k4_xboole_0(X14,X15))&(~r2_hidden(X17,X15)|~r2_hidden(X17,X16)|X16!=k4_xboole_0(X14,X15)))&(~r2_hidden(X18,X14)|r2_hidden(X18,X15)|r2_hidden(X18,X16)|X16!=k4_xboole_0(X14,X15)))&((~r2_hidden(esk2_3(X19,X20,X21),X21)|(~r2_hidden(esk2_3(X19,X20,X21),X19)|r2_hidden(esk2_3(X19,X20,X21),X20))|X21=k4_xboole_0(X19,X20))&((r2_hidden(esk2_3(X19,X20,X21),X19)|r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k4_xboole_0(X19,X20))&(~r2_hidden(esk2_3(X19,X20,X21),X20)|r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k4_xboole_0(X19,X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 2.55/2.75  fof(c_0_44, plain, ![X38, X39]:k4_xboole_0(X38,X39)=k5_xboole_0(X38,k3_xboole_0(X38,X39)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 2.55/2.75  cnf(c_0_45, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 2.55/2.75  cnf(c_0_46, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38])).
% 2.55/2.75  cnf(c_0_47, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 2.55/2.75  cnf(c_0_48, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 2.55/2.75  cnf(c_0_49, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 2.55/2.75  fof(c_0_50, plain, ![X46]:k5_xboole_0(X46,X46)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 2.55/2.75  cnf(c_0_51, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_42])).
% 2.55/2.75  fof(c_0_52, plain, ![X49, X50]:k2_xboole_0(X49,X50)=k5_xboole_0(X49,k4_xboole_0(X50,X49)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 2.55/2.75  cnf(c_0_53, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 2.55/2.75  cnf(c_0_54, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 2.55/2.75  fof(c_0_55, plain, ![X43, X44, X45]:k5_xboole_0(k5_xboole_0(X43,X44),X45)=k5_xboole_0(X43,k5_xboole_0(X44,X45)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 2.55/2.75  cnf(c_0_56, plain, (k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_48]), c_0_49])).
% 2.55/2.75  cnf(c_0_57, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_50])).
% 2.55/2.75  cnf(c_0_58, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_36]), c_0_37]), c_0_38]), c_0_47]), c_0_48]), c_0_49])).
% 2.55/2.75  cnf(c_0_59, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 2.55/2.75  cnf(c_0_60, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X4),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X4))))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54]), c_0_46]), c_0_47]), c_0_48]), c_0_49])).
% 2.55/2.75  cnf(c_0_61, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 2.55/2.75  cnf(c_0_62, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 2.55/2.75  fof(c_0_63, plain, ![X27, X28, X30, X31, X32]:(((r2_hidden(esk3_2(X27,X28),X27)|r1_xboole_0(X27,X28))&(r2_hidden(esk3_2(X27,X28),X28)|r1_xboole_0(X27,X28)))&(~r2_hidden(X32,X30)|~r2_hidden(X32,X31)|~r1_xboole_0(X30,X31))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 2.55/2.75  fof(c_0_64, plain, ![X42]:r1_xboole_0(X42,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 2.55/2.75  cnf(c_0_65, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 2.55/2.75  fof(c_0_66, plain, ![X40]:k2_xboole_0(X40,k1_xboole_0)=X40, inference(variable_rename,[status(thm)],[t1_boole])).
% 2.55/2.75  cnf(c_0_67, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_36]), c_0_54]), c_0_37]), c_0_38]), c_0_46]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_49]), c_0_49])).
% 2.55/2.75  cnf(c_0_68, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))))), inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61])])).
% 2.55/2.75  cnf(c_0_69, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_57]), c_0_62])).
% 2.55/2.75  cnf(c_0_70, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 2.55/2.75  cnf(c_0_71, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 2.55/2.75  cnf(c_0_72, plain, (X3=k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_54]), c_0_46]), c_0_47]), c_0_48]), c_0_49])).
% 2.55/2.75  cnf(c_0_73, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_66])).
% 2.55/2.75  cnf(c_0_74, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))))))), inference(rw,[status(thm)],[c_0_67, c_0_61])).
% 2.55/2.75  cnf(c_0_75, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 2.55/2.75  cnf(c_0_76, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 2.55/2.75  cnf(c_0_77, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 2.55/2.75  cnf(c_0_78, plain, (X1=k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))))|r2_hidden(esk2_3(X2,X3,X1),X2)|r2_hidden(esk2_3(X2,X3,X1),X1)), inference(rw,[status(thm)],[c_0_72, c_0_61])).
% 2.55/2.75  cnf(c_0_79, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_36]), c_0_37]), c_0_38]), c_0_47]), c_0_48]), c_0_49])).
% 2.55/2.75  cnf(c_0_80, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_69]), c_0_69])).
% 2.55/2.75  cnf(c_0_81, plain, (X3!=k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X4,X2),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_54]), c_0_46]), c_0_47]), c_0_48]), c_0_49])).
% 2.55/2.75  fof(c_0_82, negated_conjecture, ~(![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4)))), inference(assume_negation,[status(cth)],[t134_zfmisc_1])).
% 2.55/2.75  fof(c_0_83, plain, ![X80, X81, X82, X83]:(((r2_hidden(X80,X82)|~r2_hidden(k4_tarski(X80,X81),k2_zfmisc_1(X82,X83)))&(r2_hidden(X81,X83)|~r2_hidden(k4_tarski(X80,X81),k2_zfmisc_1(X82,X83))))&(~r2_hidden(X80,X82)|~r2_hidden(X81,X83)|r2_hidden(k4_tarski(X80,X81),k2_zfmisc_1(X82,X83)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 2.55/2.75  cnf(c_0_84, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_58]), c_0_57]), c_0_77])).
% 2.55/2.75  cnf(c_0_85, plain, (X1=k5_xboole_0(X2,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)))|r2_hidden(esk2_3(X3,X2,X1),X1)|r2_hidden(esk2_3(X3,X2,X1),X3)), inference(rw,[status(thm)],[c_0_78, c_0_69])).
% 2.55/2.75  cnf(c_0_86, plain, (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 2.55/2.75  cnf(c_0_87, plain, (~r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_61])])).
% 2.55/2.75  fof(c_0_88, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=k2_zfmisc_1(esk7_0,esk8_0)&((esk5_0!=k1_xboole_0&esk6_0!=k1_xboole_0)&(esk5_0!=esk7_0|esk6_0!=esk8_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_82])])])).
% 2.55/2.75  cnf(c_0_89, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 2.55/2.75  cnf(c_0_90, plain, (X1=k1_xboole_0|r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86]), c_0_57])).
% 2.55/2.75  fof(c_0_91, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 2.55/2.75  cnf(c_0_92, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_87, c_0_69])).
% 2.55/2.75  cnf(c_0_93, plain, (r2_hidden(esk3_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 2.55/2.75  fof(c_0_94, plain, ![X23, X24]:(((r1_tarski(X23,X24)|~r2_xboole_0(X23,X24))&(X23!=X24|~r2_xboole_0(X23,X24)))&(~r1_tarski(X23,X24)|X23=X24|r2_xboole_0(X23,X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 2.55/2.75  fof(c_0_95, plain, ![X41]:r1_tarski(k1_xboole_0,X41), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 2.55/2.75  cnf(c_0_96, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 2.55/2.75  cnf(c_0_97, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=k2_zfmisc_1(esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 2.55/2.75  cnf(c_0_98, plain, (X1=k1_xboole_0|r2_hidden(k4_tarski(X2,esk2_3(k1_xboole_0,X3,X1)),k2_zfmisc_1(X4,X1))|~r2_hidden(X2,X4)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 2.55/2.75  cnf(c_0_99, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 2.55/2.75  cnf(c_0_100, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk3_2(X1,X2),k5_xboole_0(X2,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))))), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 2.55/2.75  fof(c_0_101, plain, ![X33, X34]:((r2_hidden(esk4_2(X33,X34),X34)|~r2_xboole_0(X33,X34))&(~r2_hidden(esk4_2(X33,X34),X33)|~r2_xboole_0(X33,X34))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_xboole_0])])])])])).
% 2.55/2.75  cnf(c_0_102, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_94])).
% 2.55/2.75  cnf(c_0_103, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_95])).
% 2.55/2.75  cnf(c_0_104, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 2.55/2.75  cnf(c_0_105, plain, (X1=k1_xboole_0|r2_hidden(k4_tarski(esk1_2(X2,X3),esk2_3(k1_xboole_0,X4,X1)),k2_zfmisc_1(X2,X1))|r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 2.55/2.75  cnf(c_0_106, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_88])).
% 2.55/2.75  cnf(c_0_107, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_3(X3,X2,X4),X3)|r2_hidden(esk2_3(X3,X2,X4),X4)|~r2_hidden(esk3_2(X1,X2),X4)), inference(spm,[status(thm)],[c_0_100, c_0_85])).
% 2.55/2.75  cnf(c_0_108, plain, (r2_hidden(esk4_2(X1,X2),X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_101])).
% 2.55/2.75  cnf(c_0_109, plain, (k1_xboole_0=X1|r2_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 2.55/2.75  fof(c_0_110, plain, ![X87, X88, X89]:((r1_tarski(k2_zfmisc_1(X87,X89),k2_zfmisc_1(X88,X89))|~r1_tarski(X87,X88))&(r1_tarski(k2_zfmisc_1(X89,X87),k2_zfmisc_1(X89,X88))|~r1_tarski(X87,X88))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).
% 2.55/2.75  cnf(c_0_111, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 2.55/2.75  cnf(c_0_112, negated_conjecture, (r2_hidden(esk1_2(esk5_0,X1),esk7_0)|r1_tarski(esk5_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_106])).
% 2.55/2.75  cnf(c_0_113, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_3(X3,X2,X2),X2)|r2_hidden(esk2_3(X3,X2,X2),X3)), inference(spm,[status(thm)],[c_0_107, c_0_93])).
% 2.55/2.75  cnf(c_0_114, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 2.55/2.75  cnf(c_0_115, plain, (k1_xboole_0=X1|r2_hidden(esk4_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 2.55/2.75  cnf(c_0_116, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_110])).
% 2.55/2.75  cnf(c_0_117, negated_conjecture, (r1_tarski(esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_111, c_0_112])).
% 2.55/2.75  cnf(c_0_118, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_3(X2,X2,X2),X2)), inference(ef,[status(thm)],[c_0_113])).
% 2.55/2.75  cnf(c_0_119, negated_conjecture, (r2_hidden(X1,esk8_0)|~r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_114, c_0_97])).
% 2.55/2.75  cnf(c_0_120, plain, (k1_xboole_0=X1|X2=k1_xboole_0|r2_hidden(k4_tarski(esk4_2(k1_xboole_0,X1),esk2_3(k1_xboole_0,X3,X2)),k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_98, c_0_115])).
% 2.55/2.75  cnf(c_0_121, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_88])).
% 2.55/2.75  fof(c_0_122, plain, ![X84, X85, X86]:((~r1_tarski(k2_zfmisc_1(X85,X84),k2_zfmisc_1(X86,X84))|X84=k1_xboole_0|r1_tarski(X85,X86))&(~r1_tarski(k2_zfmisc_1(X84,X85),k2_zfmisc_1(X84,X86))|X84=k1_xboole_0|r1_tarski(X85,X86))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).
% 2.55/2.75  cnf(c_0_123, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk5_0,X1),k2_zfmisc_1(esk7_0,X1))), inference(spm,[status(thm)],[c_0_116, c_0_117])).
% 2.55/2.75  cnf(c_0_124, plain, (r2_hidden(esk2_3(X1,X1,X1),X1)|~r2_hidden(X2,X1)|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_70, c_0_118])).
% 2.55/2.75  cnf(c_0_125, negated_conjecture, (r2_hidden(esk2_3(k1_xboole_0,X1,esk6_0),esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_121]), c_0_106])).
% 2.55/2.75  cnf(c_0_126, plain, (X1=k1_xboole_0|r1_tarski(X2,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_122])).
% 2.55/2.75  cnf(c_0_127, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk5_0,esk8_0),k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_123, c_0_97])).
% 2.55/2.75  cnf(c_0_128, negated_conjecture, (r2_hidden(esk2_3(esk8_0,esk8_0,esk8_0),esk8_0)|~r2_hidden(esk2_3(k1_xboole_0,X1,esk6_0),X2)), inference(spm,[status(thm)],[c_0_124, c_0_125])).
% 2.55/2.75  cnf(c_0_129, negated_conjecture, (r1_tarski(esk8_0,esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_127]), c_0_121])).
% 2.55/2.75  cnf(c_0_130, negated_conjecture, (r2_hidden(esk2_3(esk8_0,esk8_0,esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_128, c_0_125])).
% 2.55/2.75  cnf(c_0_131, negated_conjecture, (esk8_0=esk6_0|r2_xboole_0(esk8_0,esk6_0)), inference(spm,[status(thm)],[c_0_102, c_0_129])).
% 2.55/2.75  cnf(c_0_132, negated_conjecture, (r2_hidden(k4_tarski(X1,esk2_3(esk8_0,esk8_0,esk8_0)),k2_zfmisc_1(X2,esk8_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_89, c_0_130])).
% 2.55/2.75  cnf(c_0_133, negated_conjecture, (r2_hidden(esk4_2(k1_xboole_0,esk5_0),esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_120]), c_0_121]), c_0_106])).
% 2.55/2.75  cnf(c_0_134, negated_conjecture, (esk8_0=esk6_0|r2_hidden(esk4_2(esk8_0,esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_108, c_0_131])).
% 2.55/2.75  cnf(c_0_135, negated_conjecture, (r2_hidden(k4_tarski(esk4_2(k1_xboole_0,esk5_0),esk2_3(esk8_0,esk8_0,esk8_0)),k2_zfmisc_1(esk5_0,esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_133]), c_0_97])).
% 2.55/2.75  cnf(c_0_136, negated_conjecture, (esk8_0=esk6_0|r2_hidden(k4_tarski(X1,esk4_2(esk8_0,esk6_0)),k2_zfmisc_1(X2,esk6_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_89, c_0_134])).
% 2.55/2.75  cnf(c_0_137, negated_conjecture, (r2_hidden(esk4_2(k1_xboole_0,esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_96, c_0_135])).
% 2.55/2.75  cnf(c_0_138, plain, (~r2_hidden(esk4_2(X1,X2),X1)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_101])).
% 2.55/2.75  cnf(c_0_139, plain, (X2=k1_xboole_0|r1_tarski(X1,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_122])).
% 2.55/2.75  cnf(c_0_140, negated_conjecture, (esk8_0=esk6_0|r2_hidden(k4_tarski(esk4_2(k1_xboole_0,esk5_0),esk4_2(esk8_0,esk6_0)),k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_136, c_0_137])).
% 2.55/2.75  cnf(c_0_141, negated_conjecture, (esk8_0=esk6_0|~r2_hidden(esk4_2(esk8_0,esk6_0),esk8_0)), inference(spm,[status(thm)],[c_0_138, c_0_131])).
% 2.55/2.75  fof(c_0_142, plain, ![X36, X37]:(((r1_tarski(X36,X37)|X36!=X37)&(r1_tarski(X37,X36)|X36!=X37))&(~r1_tarski(X36,X37)|~r1_tarski(X37,X36)|X36=X37)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 2.55/2.75  cnf(c_0_143, negated_conjecture, (esk8_0=k1_xboole_0|r1_tarski(esk7_0,X1)|~r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(X1,esk8_0))), inference(spm,[status(thm)],[c_0_139, c_0_97])).
% 2.55/2.75  cnf(c_0_144, negated_conjecture, (esk8_0=esk6_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_140]), c_0_141])).
% 2.55/2.75  cnf(c_0_145, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_142])).
% 2.55/2.75  cnf(c_0_146, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_142])).
% 2.55/2.75  cnf(c_0_147, negated_conjecture, (r1_tarski(esk7_0,X1)|~r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(X1,esk6_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_143, c_0_144]), c_0_144]), c_0_106])).
% 2.55/2.75  cnf(c_0_148, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_145])).
% 2.55/2.75  cnf(c_0_149, negated_conjecture, (esk5_0!=esk7_0|esk6_0!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_88])).
% 2.55/2.75  cnf(c_0_150, negated_conjecture, (esk7_0=esk5_0|~r1_tarski(esk7_0,esk5_0)), inference(spm,[status(thm)],[c_0_146, c_0_117])).
% 2.55/2.75  cnf(c_0_151, negated_conjecture, (r1_tarski(esk7_0,esk5_0)), inference(spm,[status(thm)],[c_0_147, c_0_148])).
% 2.55/2.75  cnf(c_0_152, negated_conjecture, (esk7_0!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_149, c_0_144])])).
% 2.55/2.75  cnf(c_0_153, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_150, c_0_151])]), c_0_152]), ['proof']).
% 2.55/2.75  # SZS output end CNFRefutation
% 2.55/2.75  # Proof object total steps             : 154
% 2.55/2.75  # Proof object clause steps            : 99
% 2.55/2.75  # Proof object formula steps           : 55
% 2.55/2.75  # Proof object conjectures             : 33
% 2.55/2.75  # Proof object clause conjectures      : 30
% 2.55/2.75  # Proof object formula conjectures     : 3
% 2.55/2.75  # Proof object initial clauses used    : 39
% 2.55/2.75  # Proof object initial formulas used   : 27
% 2.55/2.75  # Proof object generating inferences   : 38
% 2.55/2.75  # Proof object simplifying inferences  : 81
% 2.55/2.75  # Training examples: 0 positive, 0 negative
% 2.55/2.75  # Parsed axioms                        : 27
% 2.55/2.75  # Removed by relevancy pruning/SinE    : 0
% 2.55/2.75  # Initial clauses                      : 48
% 2.55/2.75  # Removed in clause preprocessing      : 9
% 2.55/2.75  # Initial clauses in saturation        : 39
% 2.55/2.75  # Processed clauses                    : 4631
% 2.55/2.75  # ...of these trivial                  : 82
% 2.55/2.75  # ...subsumed                          : 3209
% 2.55/2.75  # ...remaining for further processing  : 1340
% 2.55/2.75  # Other redundant clauses eliminated   : 6
% 2.55/2.75  # Clauses deleted for lack of memory   : 0
% 2.55/2.75  # Backward-subsumed                    : 90
% 2.55/2.75  # Backward-rewritten                   : 434
% 2.55/2.75  # Generated clauses                    : 138836
% 2.55/2.75  # ...of the previous two non-trivial   : 137460
% 2.55/2.75  # Contextual simplify-reflections      : 2
% 2.55/2.75  # Paramodulations                      : 138772
% 2.55/2.75  # Factorizations                       : 52
% 2.55/2.75  # Equation resolutions                 : 6
% 2.55/2.75  # Propositional unsat checks           : 0
% 2.55/2.75  #    Propositional check models        : 0
% 2.55/2.75  #    Propositional check unsatisfiable : 0
% 2.55/2.75  #    Propositional clauses             : 0
% 2.55/2.75  #    Propositional clauses after purity: 0
% 2.55/2.75  #    Propositional unsat core size     : 0
% 2.55/2.75  #    Propositional preprocessing time  : 0.000
% 2.55/2.75  #    Propositional encoding time       : 0.000
% 2.55/2.75  #    Propositional solver time         : 0.000
% 2.55/2.75  #    Success case prop preproc time    : 0.000
% 2.55/2.75  #    Success case prop encoding time   : 0.000
% 2.55/2.75  #    Success case prop solver time     : 0.000
% 2.55/2.75  # Current number of processed clauses  : 766
% 2.55/2.75  #    Positive orientable unit clauses  : 99
% 2.55/2.75  #    Positive unorientable unit clauses: 5
% 2.55/2.75  #    Negative unit clauses             : 30
% 2.55/2.75  #    Non-unit-clauses                  : 632
% 2.55/2.75  # Current number of unprocessed clauses: 132642
% 2.55/2.75  # ...number of literals in the above   : 577710
% 2.55/2.75  # Current number of archived formulas  : 0
% 2.55/2.75  # Current number of archived clauses   : 577
% 2.55/2.75  # Clause-clause subsumption calls (NU) : 113884
% 2.55/2.75  # Rec. Clause-clause subsumption calls : 76521
% 2.55/2.75  # Non-unit clause-clause subsumptions  : 2250
% 2.55/2.75  # Unit Clause-clause subsumption calls : 10405
% 2.55/2.75  # Rewrite failures with RHS unbound    : 0
% 2.55/2.75  # BW rewrite match attempts            : 611
% 2.55/2.75  # BW rewrite match successes           : 155
% 2.55/2.75  # Condensation attempts                : 0
% 2.55/2.75  # Condensation successes               : 0
% 2.55/2.75  # Termbank termtop insertions          : 3904145
% 2.55/2.76  
% 2.55/2.76  # -------------------------------------------------
% 2.55/2.76  # User time                : 2.364 s
% 2.55/2.76  # System time              : 0.057 s
% 2.55/2.76  # Total time               : 2.421 s
% 2.55/2.76  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
