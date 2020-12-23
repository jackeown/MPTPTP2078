%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:38:04 EST 2020

% Result     : Theorem 0.39s
% Output     : CNFRefutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 998 expanded)
%              Number of clauses        :   55 ( 444 expanded)
%              Number of leaves         :   20 ( 275 expanded)
%              Depth                    :   14
%              Number of atoms          :  171 (1290 expanded)
%              Number of equality atoms :  106 ( 907 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t20_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(t76_enumset1,axiom,(
    ! [X1] : k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t79_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k4_enumset1(X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).

fof(t81_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t6_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),k1_tarski(X2))
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(c_0_20,plain,(
    ! [X29] :
      ( ~ r1_tarski(X29,k1_xboole_0)
      | X29 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

fof(c_0_21,plain,(
    ! [X27,X28] : r1_tarski(k4_xboole_0(X27,X28),X27) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_22,plain,(
    ! [X36,X37] : k3_xboole_0(X36,X37) = k5_xboole_0(k5_xboole_0(X36,X37),k2_xboole_0(X36,X37)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

fof(c_0_23,plain,(
    ! [X38,X39] : k2_xboole_0(X38,X39) = k5_xboole_0(X38,k4_xboole_0(X39,X38)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_24,plain,(
    ! [X25] : k2_xboole_0(X25,k1_xboole_0) = X25 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_25,plain,(
    ! [X23,X24] :
      ( ( k4_xboole_0(X23,X24) != k1_xboole_0
        | r1_tarski(X23,X24) )
      & ( ~ r1_tarski(X23,X24)
        | k4_xboole_0(X23,X24) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X26] : k3_xboole_0(X26,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_32,plain,(
    ! [X15,X16,X18,X19,X20] :
      ( ( r1_xboole_0(X15,X16)
        | r2_hidden(esk2_2(X15,X16),k3_xboole_0(X15,X16)) )
      & ( ~ r2_hidden(X20,k3_xboole_0(X18,X19))
        | ~ r1_xboole_0(X18,X19) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_33,plain,(
    ! [X30,X31,X32] :
      ( ~ r1_tarski(X30,X31)
      | r1_xboole_0(X30,k4_xboole_0(X32,X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_38,plain,(
    ! [X33,X34,X35] : k5_xboole_0(k5_xboole_0(X33,X34),X35) = k5_xboole_0(X33,k5_xboole_0(X34,X35)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_39,plain,(
    ! [X7,X8] : k5_xboole_0(X7,X8) = k5_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_45,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_46,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_40,c_0_35])).

fof(c_0_49,plain,(
    ! [X21] :
      ( X21 = k1_xboole_0
      | r2_hidden(esk3_1(X21),X21) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_50,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k5_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(X2,k4_xboole_0(X3,X2)))) ),
    inference(rw,[status(thm)],[c_0_41,c_0_37])).

cnf(c_0_51,plain,
    ( r1_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_27])).

fof(c_0_53,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
      <=> X1 != X2 ) ),
    inference(assume_negation,[status(cth)],[t20_zfmisc_1])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_40]),c_0_46])).

cnf(c_0_55,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,k4_xboole_0(X3,X2)))))
    | ~ r1_xboole_0(X2,X3) ),
    inference(rw,[status(thm)],[c_0_50,c_0_46])).

cnf(c_0_58,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

fof(c_0_59,negated_conjecture,
    ( ( k4_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)) != k1_tarski(esk5_0)
      | esk5_0 = esk6_0 )
    & ( k4_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)) = k1_tarski(esk5_0)
      | esk5_0 != esk6_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_53])])])).

fof(c_0_60,plain,(
    ! [X50] : k1_enumset1(X50,X50,X50) = k1_tarski(X50) ),
    inference(variable_rename,[status(thm)],[t76_enumset1])).

fof(c_0_61,plain,(
    ! [X47,X48,X49] : k2_enumset1(X47,X47,X48,X49) = k1_enumset1(X47,X48,X49) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_62,plain,(
    ! [X51,X52,X53,X54] : k4_enumset1(X51,X51,X51,X52,X53,X54) = k2_enumset1(X51,X52,X53,X54) ),
    inference(variable_rename,[status(thm)],[t79_enumset1])).

fof(c_0_63,plain,(
    ! [X55,X56,X57,X58,X59,X60] : k6_enumset1(X55,X55,X55,X56,X57,X58,X59,X60) = k4_enumset1(X55,X56,X57,X58,X59,X60) ),
    inference(variable_rename,[status(thm)],[t81_enumset1])).

cnf(c_0_64,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_65,plain,
    ( X1 = X2
    | r2_hidden(esk3_1(X2),X2)
    | r2_hidden(esk3_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_56])).

cnf(c_0_66,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_35]),c_0_55]),c_0_55]),c_0_55])).

cnf(c_0_67,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)) = k1_tarski(esk5_0)
    | esk5_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,plain,
    ( k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_71,plain,
    ( k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_64]),c_0_55])).

cnf(c_0_73,plain,
    ( k5_xboole_0(X1,X2) = X1
    | r2_hidden(esk3_1(X2),X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_65]),c_0_66])).

fof(c_0_74,plain,(
    ! [X61,X62] :
      ( ( ~ r1_tarski(X61,k1_tarski(X62))
        | X61 = k1_xboole_0
        | X61 = k1_tarski(X62) )
      & ( X61 != k1_xboole_0
        | r1_tarski(X61,k1_tarski(X62)) )
      & ( X61 != k1_tarski(X62)
        | r1_tarski(X61,k1_tarski(X62)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

fof(c_0_75,plain,(
    ! [X40,X41,X42,X43,X44,X45] :
      ( ( ~ r2_hidden(X42,X41)
        | X42 = X40
        | X41 != k1_tarski(X40) )
      & ( X43 != X40
        | r2_hidden(X43,X41)
        | X41 != k1_tarski(X40) )
      & ( ~ r2_hidden(esk4_2(X44,X45),X45)
        | esk4_2(X44,X45) != X44
        | X45 = k1_tarski(X44) )
      & ( r2_hidden(esk4_2(X44,X45),X45)
        | esk4_2(X44,X45) = X44
        | X45 = k1_tarski(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_76,negated_conjecture,
    ( k4_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) = k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)
    | esk6_0 != esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68]),c_0_68]),c_0_68]),c_0_69]),c_0_69]),c_0_69]),c_0_70]),c_0_70]),c_0_70]),c_0_71]),c_0_71]),c_0_71])).

cnf(c_0_77,plain,
    ( X1 = X2
    | r2_hidden(esk3_1(k5_xboole_0(X1,X2)),k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_78,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( k4_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) = k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)
    | r2_hidden(esk3_1(k5_xboole_0(esk5_0,esk6_0)),k5_xboole_0(esk5_0,esk6_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77])])).

cnf(c_0_81,negated_conjecture,
    ( esk5_0 = esk6_0
    | k4_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)) != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_82,plain,
    ( X1 = k1_xboole_0
    | X1 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_68]),c_0_68]),c_0_69]),c_0_69]),c_0_70]),c_0_70]),c_0_71]),c_0_71])).

fof(c_0_83,plain,(
    ! [X63,X64] :
      ( ~ r1_tarski(k1_tarski(X63),k1_tarski(X64))
      | X63 = X64 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_zfmisc_1])])).

cnf(c_0_84,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_68]),c_0_69]),c_0_70]),c_0_71])).

cnf(c_0_85,negated_conjecture,
    ( k4_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) = k1_xboole_0
    | r2_hidden(esk3_1(k5_xboole_0(esk5_0,esk6_0)),k5_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( esk6_0 = esk5_0
    | k4_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) != k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_68]),c_0_68]),c_0_68]),c_0_69]),c_0_69]),c_0_69]),c_0_70]),c_0_70]),c_0_70]),c_0_71]),c_0_71]),c_0_71])).

cnf(c_0_87,plain,
    ( k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_82,c_0_27])).

cnf(c_0_88,plain,
    ( X1 = X2
    | ~ r1_tarski(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_89,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_84])])).

cnf(c_0_90,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k1_xboole_0
    | r2_hidden(esk3_1(k5_xboole_0(esk5_0,esk6_0)),k5_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_85])).

cnf(c_0_91,negated_conjecture,
    ( k4_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) = k1_xboole_0
    | esk6_0 = esk5_0 ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_92,plain,
    ( X1 = X2
    | ~ r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_68]),c_0_68]),c_0_69]),c_0_69]),c_0_70]),c_0_70]),c_0_71]),c_0_71])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk3_1(k5_xboole_0(esk5_0,esk6_0)),k5_xboole_0(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_66])).

cnf(c_0_94,negated_conjecture,
    ( esk6_0 = esk5_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_91]),c_0_92])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_94]),c_0_64]),c_0_94]),c_0_64]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:36:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.39/0.57  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.39/0.57  # and selection function SelectNegativeLiterals.
% 0.39/0.57  #
% 0.39/0.57  # Preprocessing time       : 0.040 s
% 0.39/0.57  # Presaturation interreduction done
% 0.39/0.57  
% 0.39/0.57  # Proof found!
% 0.39/0.57  # SZS status Theorem
% 0.39/0.57  # SZS output start CNFRefutation
% 0.39/0.57  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.39/0.57  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.39/0.57  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.39/0.57  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.39/0.57  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.39/0.57  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.39/0.57  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.39/0.57  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.39/0.57  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 0.39/0.57  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.39/0.57  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.39/0.57  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.39/0.57  fof(t20_zfmisc_1, conjecture, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.39/0.57  fof(t76_enumset1, axiom, ![X1]:k1_enumset1(X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_enumset1)).
% 0.39/0.57  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.39/0.57  fof(t79_enumset1, axiom, ![X1, X2, X3, X4]:k4_enumset1(X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_enumset1)).
% 0.39/0.57  fof(t81_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_enumset1)).
% 0.39/0.57  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.39/0.57  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.39/0.57  fof(t6_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),k1_tarski(X2))=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 0.39/0.57  fof(c_0_20, plain, ![X29]:(~r1_tarski(X29,k1_xboole_0)|X29=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.39/0.57  fof(c_0_21, plain, ![X27, X28]:r1_tarski(k4_xboole_0(X27,X28),X27), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.39/0.57  fof(c_0_22, plain, ![X36, X37]:k3_xboole_0(X36,X37)=k5_xboole_0(k5_xboole_0(X36,X37),k2_xboole_0(X36,X37)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.39/0.57  fof(c_0_23, plain, ![X38, X39]:k2_xboole_0(X38,X39)=k5_xboole_0(X38,k4_xboole_0(X39,X38)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.39/0.57  fof(c_0_24, plain, ![X25]:k2_xboole_0(X25,k1_xboole_0)=X25, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.39/0.57  fof(c_0_25, plain, ![X23, X24]:((k4_xboole_0(X23,X24)!=k1_xboole_0|r1_tarski(X23,X24))&(~r1_tarski(X23,X24)|k4_xboole_0(X23,X24)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.39/0.57  cnf(c_0_26, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.39/0.57  cnf(c_0_27, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.39/0.57  fof(c_0_28, plain, ![X26]:k3_xboole_0(X26,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.39/0.57  cnf(c_0_29, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.39/0.57  cnf(c_0_30, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.39/0.57  cnf(c_0_31, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.39/0.57  fof(c_0_32, plain, ![X15, X16, X18, X19, X20]:((r1_xboole_0(X15,X16)|r2_hidden(esk2_2(X15,X16),k3_xboole_0(X15,X16)))&(~r2_hidden(X20,k3_xboole_0(X18,X19))|~r1_xboole_0(X18,X19))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.39/0.57  fof(c_0_33, plain, ![X30, X31, X32]:(~r1_tarski(X30,X31)|r1_xboole_0(X30,k4_xboole_0(X32,X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 0.39/0.57  cnf(c_0_34, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.39/0.57  cnf(c_0_35, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.39/0.57  cnf(c_0_36, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.39/0.57  cnf(c_0_37, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,k4_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.39/0.57  fof(c_0_38, plain, ![X33, X34, X35]:k5_xboole_0(k5_xboole_0(X33,X34),X35)=k5_xboole_0(X33,k5_xboole_0(X34,X35)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.39/0.57  fof(c_0_39, plain, ![X7, X8]:k5_xboole_0(X7,X8)=k5_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.39/0.57  cnf(c_0_40, plain, (k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1))=X1), inference(rw,[status(thm)],[c_0_31, c_0_30])).
% 0.39/0.57  cnf(c_0_41, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.39/0.57  cnf(c_0_42, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.39/0.57  cnf(c_0_43, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.39/0.57  cnf(c_0_44, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.39/0.57  cnf(c_0_45, plain, (k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.39/0.57  cnf(c_0_46, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.39/0.57  cnf(c_0_47, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.39/0.57  cnf(c_0_48, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_40, c_0_35])).
% 0.39/0.57  fof(c_0_49, plain, ![X21]:(X21=k1_xboole_0|r2_hidden(esk3_1(X21),X21)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.39/0.57  cnf(c_0_50, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k5_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(X2,k4_xboole_0(X3,X2))))), inference(rw,[status(thm)],[c_0_41, c_0_37])).
% 0.39/0.57  cnf(c_0_51, plain, (r1_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.39/0.57  cnf(c_0_52, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_27])).
% 0.39/0.57  fof(c_0_53, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2)), inference(assume_negation,[status(cth)],[t20_zfmisc_1])).
% 0.39/0.57  cnf(c_0_54, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_40]), c_0_46])).
% 0.39/0.57  cnf(c_0_55, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.39/0.57  cnf(c_0_56, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.39/0.57  cnf(c_0_57, plain, (~r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,k4_xboole_0(X3,X2)))))|~r1_xboole_0(X2,X3)), inference(rw,[status(thm)],[c_0_50, c_0_46])).
% 0.39/0.57  cnf(c_0_58, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.39/0.57  fof(c_0_59, negated_conjecture, ((k4_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))!=k1_tarski(esk5_0)|esk5_0=esk6_0)&(k4_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))=k1_tarski(esk5_0)|esk5_0!=esk6_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_53])])])).
% 0.39/0.57  fof(c_0_60, plain, ![X50]:k1_enumset1(X50,X50,X50)=k1_tarski(X50), inference(variable_rename,[status(thm)],[t76_enumset1])).
% 0.39/0.57  fof(c_0_61, plain, ![X47, X48, X49]:k2_enumset1(X47,X47,X48,X49)=k1_enumset1(X47,X48,X49), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.39/0.57  fof(c_0_62, plain, ![X51, X52, X53, X54]:k4_enumset1(X51,X51,X51,X52,X53,X54)=k2_enumset1(X51,X52,X53,X54), inference(variable_rename,[status(thm)],[t79_enumset1])).
% 0.39/0.57  fof(c_0_63, plain, ![X55, X56, X57, X58, X59, X60]:k6_enumset1(X55,X55,X55,X56,X57,X58,X59,X60)=k4_enumset1(X55,X56,X57,X58,X59,X60), inference(variable_rename,[status(thm)],[t81_enumset1])).
% 0.39/0.57  cnf(c_0_64, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_54, c_0_55])).
% 0.39/0.57  cnf(c_0_65, plain, (X1=X2|r2_hidden(esk3_1(X2),X2)|r2_hidden(esk3_1(X1),X1)), inference(spm,[status(thm)],[c_0_56, c_0_56])).
% 0.39/0.57  cnf(c_0_66, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_35]), c_0_55]), c_0_55]), c_0_55])).
% 0.39/0.57  cnf(c_0_67, negated_conjecture, (k4_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))=k1_tarski(esk5_0)|esk5_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.39/0.57  cnf(c_0_68, plain, (k1_enumset1(X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.39/0.57  cnf(c_0_69, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.39/0.57  cnf(c_0_70, plain, (k4_enumset1(X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.39/0.57  cnf(c_0_71, plain, (k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.39/0.57  cnf(c_0_72, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_64]), c_0_55])).
% 0.39/0.57  cnf(c_0_73, plain, (k5_xboole_0(X1,X2)=X1|r2_hidden(esk3_1(X2),X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_65]), c_0_66])).
% 0.39/0.57  fof(c_0_74, plain, ![X61, X62]:((~r1_tarski(X61,k1_tarski(X62))|(X61=k1_xboole_0|X61=k1_tarski(X62)))&((X61!=k1_xboole_0|r1_tarski(X61,k1_tarski(X62)))&(X61!=k1_tarski(X62)|r1_tarski(X61,k1_tarski(X62))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.39/0.57  fof(c_0_75, plain, ![X40, X41, X42, X43, X44, X45]:(((~r2_hidden(X42,X41)|X42=X40|X41!=k1_tarski(X40))&(X43!=X40|r2_hidden(X43,X41)|X41!=k1_tarski(X40)))&((~r2_hidden(esk4_2(X44,X45),X45)|esk4_2(X44,X45)!=X44|X45=k1_tarski(X44))&(r2_hidden(esk4_2(X44,X45),X45)|esk4_2(X44,X45)=X44|X45=k1_tarski(X44)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.39/0.57  cnf(c_0_76, negated_conjecture, (k4_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)|esk6_0!=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_68]), c_0_68]), c_0_68]), c_0_69]), c_0_69]), c_0_69]), c_0_70]), c_0_70]), c_0_70]), c_0_71]), c_0_71]), c_0_71])).
% 0.39/0.57  cnf(c_0_77, plain, (X1=X2|r2_hidden(esk3_1(k5_xboole_0(X1,X2)),k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.39/0.57  cnf(c_0_78, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.39/0.57  cnf(c_0_79, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.39/0.57  cnf(c_0_80, negated_conjecture, (k4_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)|r2_hidden(esk3_1(k5_xboole_0(esk5_0,esk6_0)),k5_xboole_0(esk5_0,esk6_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77])])).
% 0.39/0.57  cnf(c_0_81, negated_conjecture, (esk5_0=esk6_0|k4_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.39/0.57  cnf(c_0_82, plain, (X1=k1_xboole_0|X1=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|~r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_68]), c_0_68]), c_0_69]), c_0_69]), c_0_70]), c_0_70]), c_0_71]), c_0_71])).
% 0.39/0.57  fof(c_0_83, plain, ![X63, X64]:(~r1_tarski(k1_tarski(X63),k1_tarski(X64))|X63=X64), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_zfmisc_1])])).
% 0.39/0.57  cnf(c_0_84, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_68]), c_0_69]), c_0_70]), c_0_71])).
% 0.39/0.57  cnf(c_0_85, negated_conjecture, (k4_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))=k1_xboole_0|r2_hidden(esk3_1(k5_xboole_0(esk5_0,esk6_0)),k5_xboole_0(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_52, c_0_80])).
% 0.39/0.57  cnf(c_0_86, negated_conjecture, (esk6_0=esk5_0|k4_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))!=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_68]), c_0_68]), c_0_68]), c_0_69]), c_0_69]), c_0_69]), c_0_70]), c_0_70]), c_0_70]), c_0_71]), c_0_71]), c_0_71])).
% 0.39/0.57  cnf(c_0_87, plain, (k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)|k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_82, c_0_27])).
% 0.39/0.57  cnf(c_0_88, plain, (X1=X2|~r1_tarski(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.39/0.57  cnf(c_0_89, plain, (r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_84])])).
% 0.39/0.57  cnf(c_0_90, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k1_xboole_0|r2_hidden(esk3_1(k5_xboole_0(esk5_0,esk6_0)),k5_xboole_0(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_80, c_0_85])).
% 0.39/0.57  cnf(c_0_91, negated_conjecture, (k4_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))=k1_xboole_0|esk6_0=esk5_0), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.39/0.57  cnf(c_0_92, plain, (X1=X2|~r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_68]), c_0_68]), c_0_69]), c_0_69]), c_0_70]), c_0_70]), c_0_71]), c_0_71])).
% 0.39/0.57  cnf(c_0_93, negated_conjecture, (r2_hidden(esk3_1(k5_xboole_0(esk5_0,esk6_0)),k5_xboole_0(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_66])).
% 0.39/0.57  cnf(c_0_94, negated_conjecture, (esk6_0=esk5_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_91]), c_0_92])).
% 0.39/0.57  cnf(c_0_95, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_94]), c_0_64]), c_0_94]), c_0_64]), c_0_66]), ['proof']).
% 0.39/0.57  # SZS output end CNFRefutation
% 0.39/0.57  # Proof object total steps             : 96
% 0.39/0.57  # Proof object clause steps            : 55
% 0.39/0.57  # Proof object formula steps           : 41
% 0.39/0.57  # Proof object conjectures             : 14
% 0.39/0.57  # Proof object clause conjectures      : 11
% 0.39/0.57  # Proof object formula conjectures     : 3
% 0.39/0.57  # Proof object initial clauses used    : 22
% 0.39/0.57  # Proof object initial formulas used   : 20
% 0.39/0.57  # Proof object generating inferences   : 18
% 0.39/0.57  # Proof object simplifying inferences  : 69
% 0.39/0.57  # Training examples: 0 positive, 0 negative
% 0.39/0.57  # Parsed axioms                        : 21
% 0.39/0.57  # Removed by relevancy pruning/SinE    : 0
% 0.39/0.57  # Initial clauses                      : 31
% 0.39/0.57  # Removed in clause preprocessing      : 6
% 0.39/0.57  # Initial clauses in saturation        : 25
% 0.39/0.57  # Processed clauses                    : 1379
% 0.39/0.57  # ...of these trivial                  : 16
% 0.39/0.57  # ...subsumed                          : 1090
% 0.39/0.57  # ...remaining for further processing  : 273
% 0.39/0.57  # Other redundant clauses eliminated   : 253
% 0.39/0.57  # Clauses deleted for lack of memory   : 0
% 0.39/0.57  # Backward-subsumed                    : 29
% 0.39/0.57  # Backward-rewritten                   : 73
% 0.39/0.57  # Generated clauses                    : 12652
% 0.39/0.57  # ...of the previous two non-trivial   : 11536
% 0.39/0.57  # Contextual simplify-reflections      : 2
% 0.39/0.57  # Paramodulations                      : 12384
% 0.39/0.57  # Factorizations                       : 15
% 0.39/0.57  # Equation resolutions                 : 254
% 0.39/0.57  # Propositional unsat checks           : 0
% 0.39/0.57  #    Propositional check models        : 0
% 0.39/0.57  #    Propositional check unsatisfiable : 0
% 0.39/0.57  #    Propositional clauses             : 0
% 0.39/0.57  #    Propositional clauses after purity: 0
% 0.39/0.57  #    Propositional unsat core size     : 0
% 0.39/0.57  #    Propositional preprocessing time  : 0.000
% 0.39/0.57  #    Propositional encoding time       : 0.000
% 0.39/0.57  #    Propositional solver time         : 0.000
% 0.39/0.57  #    Success case prop preproc time    : 0.000
% 0.39/0.57  #    Success case prop encoding time   : 0.000
% 0.39/0.57  #    Success case prop solver time     : 0.000
% 0.39/0.57  # Current number of processed clauses  : 142
% 0.39/0.57  #    Positive orientable unit clauses  : 26
% 0.39/0.57  #    Positive unorientable unit clauses: 3
% 0.39/0.57  #    Negative unit clauses             : 14
% 0.39/0.57  #    Non-unit-clauses                  : 99
% 0.39/0.57  # Current number of unprocessed clauses: 9743
% 0.39/0.57  # ...number of literals in the above   : 35492
% 0.39/0.57  # Current number of archived formulas  : 0
% 0.39/0.57  # Current number of archived clauses   : 133
% 0.39/0.57  # Clause-clause subsumption calls (NU) : 8034
% 0.39/0.57  # Rec. Clause-clause subsumption calls : 6524
% 0.39/0.57  # Non-unit clause-clause subsumptions  : 688
% 0.39/0.57  # Unit Clause-clause subsumption calls : 165
% 0.39/0.57  # Rewrite failures with RHS unbound    : 0
% 0.39/0.57  # BW rewrite match attempts            : 104
% 0.39/0.57  # BW rewrite match successes           : 64
% 0.39/0.57  # Condensation attempts                : 0
% 0.39/0.57  # Condensation successes               : 0
% 0.39/0.57  # Termbank termtop insertions          : 225725
% 0.39/0.57  
% 0.39/0.57  # -------------------------------------------------
% 0.39/0.57  # User time                : 0.216 s
% 0.39/0.57  # System time              : 0.014 s
% 0.39/0.57  # Total time               : 0.230 s
% 0.39/0.57  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
