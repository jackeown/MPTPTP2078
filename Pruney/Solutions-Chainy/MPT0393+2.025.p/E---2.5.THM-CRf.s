%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:12 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 567 expanded)
%              Number of clauses        :   37 ( 208 expanded)
%              Number of leaves         :   20 ( 179 expanded)
%              Depth                    :   10
%              Number of atoms          :  129 ( 651 expanded)
%              Number of equality atoms :   93 ( 590 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

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

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_setfam_1,axiom,(
    ! [X1] : r1_tarski(k1_setfam_1(X1),k3_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_setfam_1)).

fof(t6_setfam_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X2,X3) )
     => ( X1 = k1_xboole_0
        | r1_tarski(X2,k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

fof(t11_setfam_1,conjecture,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(c_0_20,plain,(
    ! [X64,X65] : k3_tarski(k2_tarski(X64,X65)) = k2_xboole_0(X64,X65) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X37,X38] : k1_enumset1(X37,X37,X38) = k2_tarski(X37,X38) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X19,X20] : k3_xboole_0(X19,X20) = k5_xboole_0(k5_xboole_0(X19,X20),k2_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_23,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X39,X40,X41] : k2_enumset1(X39,X39,X40,X41) = k1_enumset1(X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X42,X43,X44,X45] : k3_enumset1(X42,X42,X43,X44,X45) = k2_enumset1(X42,X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_27,plain,(
    ! [X21,X22,X23,X24,X25,X26] :
      ( ( ~ r2_hidden(X23,X22)
        | X23 = X21
        | X22 != k1_tarski(X21) )
      & ( X24 != X21
        | r2_hidden(X24,X22)
        | X22 != k1_tarski(X21) )
      & ( ~ r2_hidden(esk1_2(X25,X26),X26)
        | esk1_2(X25,X26) != X25
        | X26 = k1_tarski(X25) )
      & ( r2_hidden(esk1_2(X25,X26),X26)
        | esk1_2(X25,X26) = X25
        | X26 = k1_tarski(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_28,plain,(
    ! [X36] : k2_tarski(X36,X36) = k1_tarski(X36) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_29,plain,(
    ! [X46,X47,X48,X49,X50] : k4_enumset1(X46,X46,X47,X48,X49,X50) = k3_enumset1(X46,X47,X48,X49,X50) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_30,plain,(
    ! [X51,X52,X53,X54,X55,X56] : k5_enumset1(X51,X51,X52,X53,X54,X55,X56) = k4_enumset1(X51,X52,X53,X54,X55,X56) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_31,plain,(
    ! [X57,X58,X59,X60,X61,X62,X63] : k6_enumset1(X57,X57,X58,X59,X60,X61,X62,X63) = k5_enumset1(X57,X58,X59,X60,X61,X62,X63) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_32,plain,(
    ! [X66,X67] :
      ( ( k4_xboole_0(k1_tarski(X66),k1_tarski(X67)) != k1_tarski(X66)
        | X66 != X67 )
      & ( X66 = X67
        | k4_xboole_0(k1_tarski(X66),k1_tarski(X67)) = k1_tarski(X66) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

fof(c_0_33,plain,(
    ! [X12,X13] : k4_xboole_0(X12,X13) = k5_xboole_0(X12,k3_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_36,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_38,plain,(
    ! [X9] : k2_xboole_0(X9,X9) = X9 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_39,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37])).

fof(c_0_47,plain,(
    ! [X15,X16,X17] : k5_xboole_0(k5_xboole_0(X15,X16),X17) = k5_xboole_0(X15,k5_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_48,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_49,plain,(
    ! [X18] : k5_xboole_0(X18,X18) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_50,plain,(
    ! [X14] : k5_xboole_0(X14,k1_xboole_0) = X14 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_51,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_52,plain,(
    ! [X68] : r1_tarski(k1_setfam_1(X68),k3_tarski(X68)) ),
    inference(variable_rename,[status(thm)],[t3_setfam_1])).

cnf(c_0_53,plain,
    ( X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40]),c_0_24]),c_0_36]),c_0_37]),c_0_41]),c_0_42]),c_0_43])).

fof(c_0_54,plain,(
    ! [X69,X70] :
      ( ( r2_hidden(esk2_2(X69,X70),X69)
        | X69 = k1_xboole_0
        | r1_tarski(X70,k1_setfam_1(X69)) )
      & ( ~ r1_tarski(X70,esk2_2(X69,X70))
        | X69 = k1_xboole_0
        | r1_tarski(X70,k1_setfam_1(X69)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).

cnf(c_0_55,plain,
    ( X1 != X2
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_40]),c_0_40]),c_0_40]),c_0_24]),c_0_24]),c_0_24]),c_0_45]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_46]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43])).

cnf(c_0_56,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_35]),c_0_36]),c_0_37]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_60,negated_conjecture,(
    ~ ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t11_setfam_1])).

cnf(c_0_61,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,plain,
    ( r1_tarski(k1_setfam_1(X1),k3_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_64,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | X1 = k1_xboole_0
    | r1_tarski(X2,k1_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_65,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56])]),c_0_57]),c_0_58]),c_0_59]),c_0_58])).

fof(c_0_66,negated_conjecture,(
    k1_setfam_1(k1_tarski(esk3_0)) != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_60])])])).

cnf(c_0_67,plain,
    ( k3_tarski(X1) = k1_setfam_1(X1)
    | ~ r1_tarski(k3_tarski(X1),k1_setfam_1(X1)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_68,plain,
    ( esk2_2(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2) = X1
    | r1_tarski(X2,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_70,negated_conjecture,
    ( k1_setfam_1(k1_tarski(esk3_0)) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_71,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,k1_setfam_1(X2))
    | ~ r1_tarski(X1,esk2_2(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_72,plain,
    ( esk2_2(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X1) = X1
    | k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_57]),c_0_57])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_69])).

cnf(c_0_74,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1
    | ~ r1_tarski(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_57])).

cnf(c_0_75,negated_conjecture,
    ( k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) != esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_40]),c_0_24]),c_0_36]),c_0_37]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_76,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])]),c_0_65]),c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:41:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.20/0.41  # and selection function GSelectMinInfpos.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.027 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.20/0.41  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.41  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.20/0.41  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.41  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.41  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.20/0.41  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.41  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.41  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.41  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.20/0.41  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.20/0.41  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.41  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.20/0.41  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.20/0.41  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.20/0.41  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.20/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.41  fof(t3_setfam_1, axiom, ![X1]:r1_tarski(k1_setfam_1(X1),k3_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_setfam_1)).
% 0.20/0.41  fof(t6_setfam_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X2,X3))=>(X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_setfam_1)).
% 0.20/0.41  fof(t11_setfam_1, conjecture, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 0.20/0.41  fof(c_0_20, plain, ![X64, X65]:k3_tarski(k2_tarski(X64,X65))=k2_xboole_0(X64,X65), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.20/0.41  fof(c_0_21, plain, ![X37, X38]:k1_enumset1(X37,X37,X38)=k2_tarski(X37,X38), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.41  fof(c_0_22, plain, ![X19, X20]:k3_xboole_0(X19,X20)=k5_xboole_0(k5_xboole_0(X19,X20),k2_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.20/0.41  cnf(c_0_23, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.41  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.41  fof(c_0_25, plain, ![X39, X40, X41]:k2_enumset1(X39,X39,X40,X41)=k1_enumset1(X39,X40,X41), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.41  fof(c_0_26, plain, ![X42, X43, X44, X45]:k3_enumset1(X42,X42,X43,X44,X45)=k2_enumset1(X42,X43,X44,X45), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.41  fof(c_0_27, plain, ![X21, X22, X23, X24, X25, X26]:(((~r2_hidden(X23,X22)|X23=X21|X22!=k1_tarski(X21))&(X24!=X21|r2_hidden(X24,X22)|X22!=k1_tarski(X21)))&((~r2_hidden(esk1_2(X25,X26),X26)|esk1_2(X25,X26)!=X25|X26=k1_tarski(X25))&(r2_hidden(esk1_2(X25,X26),X26)|esk1_2(X25,X26)=X25|X26=k1_tarski(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.20/0.41  fof(c_0_28, plain, ![X36]:k2_tarski(X36,X36)=k1_tarski(X36), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.41  fof(c_0_29, plain, ![X46, X47, X48, X49, X50]:k4_enumset1(X46,X46,X47,X48,X49,X50)=k3_enumset1(X46,X47,X48,X49,X50), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.41  fof(c_0_30, plain, ![X51, X52, X53, X54, X55, X56]:k5_enumset1(X51,X51,X52,X53,X54,X55,X56)=k4_enumset1(X51,X52,X53,X54,X55,X56), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.41  fof(c_0_31, plain, ![X57, X58, X59, X60, X61, X62, X63]:k6_enumset1(X57,X57,X58,X59,X60,X61,X62,X63)=k5_enumset1(X57,X58,X59,X60,X61,X62,X63), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.20/0.41  fof(c_0_32, plain, ![X66, X67]:((k4_xboole_0(k1_tarski(X66),k1_tarski(X67))!=k1_tarski(X66)|X66!=X67)&(X66=X67|k4_xboole_0(k1_tarski(X66),k1_tarski(X67))=k1_tarski(X66))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 0.20/0.41  fof(c_0_33, plain, ![X12, X13]:k4_xboole_0(X12,X13)=k5_xboole_0(X12,k3_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.41  cnf(c_0_34, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.41  cnf(c_0_35, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.41  cnf(c_0_36, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.41  cnf(c_0_37, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.41  fof(c_0_38, plain, ![X9]:k2_xboole_0(X9,X9)=X9, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.20/0.41  cnf(c_0_39, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.41  cnf(c_0_40, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.41  cnf(c_0_41, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.41  cnf(c_0_42, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.41  cnf(c_0_43, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.41  cnf(c_0_44, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.41  cnf(c_0_45, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.41  cnf(c_0_46, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37])).
% 0.20/0.41  fof(c_0_47, plain, ![X15, X16, X17]:k5_xboole_0(k5_xboole_0(X15,X16),X17)=k5_xboole_0(X15,k5_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.20/0.41  cnf(c_0_48, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.41  fof(c_0_49, plain, ![X18]:k5_xboole_0(X18,X18)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.20/0.41  fof(c_0_50, plain, ![X14]:k5_xboole_0(X14,k1_xboole_0)=X14, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.20/0.41  fof(c_0_51, plain, ![X10, X11]:(((r1_tarski(X10,X11)|X10!=X11)&(r1_tarski(X11,X10)|X10!=X11))&(~r1_tarski(X10,X11)|~r1_tarski(X11,X10)|X10=X11)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.41  fof(c_0_52, plain, ![X68]:r1_tarski(k1_setfam_1(X68),k3_tarski(X68)), inference(variable_rename,[status(thm)],[t3_setfam_1])).
% 0.20/0.41  cnf(c_0_53, plain, (X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40]), c_0_24]), c_0_36]), c_0_37]), c_0_41]), c_0_42]), c_0_43])).
% 0.20/0.41  fof(c_0_54, plain, ![X69, X70]:((r2_hidden(esk2_2(X69,X70),X69)|(X69=k1_xboole_0|r1_tarski(X70,k1_setfam_1(X69))))&(~r1_tarski(X70,esk2_2(X69,X70))|(X69=k1_xboole_0|r1_tarski(X70,k1_setfam_1(X69))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).
% 0.20/0.41  cnf(c_0_55, plain, (X1!=X2|k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))!=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_40]), c_0_40]), c_0_40]), c_0_24]), c_0_24]), c_0_24]), c_0_45]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_46]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43])).
% 0.20/0.41  cnf(c_0_56, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.41  cnf(c_0_57, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_35]), c_0_36]), c_0_37]), c_0_41]), c_0_42]), c_0_43])).
% 0.20/0.41  cnf(c_0_58, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.41  cnf(c_0_59, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.41  fof(c_0_60, negated_conjecture, ~(![X1]:k1_setfam_1(k1_tarski(X1))=X1), inference(assume_negation,[status(cth)],[t11_setfam_1])).
% 0.20/0.41  cnf(c_0_61, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.41  cnf(c_0_62, plain, (r1_tarski(k1_setfam_1(X1),k3_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.41  cnf(c_0_63, plain, (X1=X2|~r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_53])).
% 0.20/0.41  cnf(c_0_64, plain, (r2_hidden(esk2_2(X1,X2),X1)|X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.41  cnf(c_0_65, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56])]), c_0_57]), c_0_58]), c_0_59]), c_0_58])).
% 0.20/0.41  fof(c_0_66, negated_conjecture, k1_setfam_1(k1_tarski(esk3_0))!=esk3_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_60])])])).
% 0.20/0.41  cnf(c_0_67, plain, (k3_tarski(X1)=k1_setfam_1(X1)|~r1_tarski(k3_tarski(X1),k1_setfam_1(X1))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.41  cnf(c_0_68, plain, (esk2_2(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)=X1|r1_tarski(X2,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])).
% 0.20/0.41  cnf(c_0_69, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.41  cnf(c_0_70, negated_conjecture, (k1_setfam_1(k1_tarski(esk3_0))!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.20/0.41  cnf(c_0_71, plain, (X2=k1_xboole_0|r1_tarski(X1,k1_setfam_1(X2))|~r1_tarski(X1,esk2_2(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.41  cnf(c_0_72, plain, (esk2_2(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X1)=X1|k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_57]), c_0_57])).
% 0.20/0.41  cnf(c_0_73, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_69])).
% 0.20/0.41  cnf(c_0_74, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1|~r1_tarski(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))), inference(spm,[status(thm)],[c_0_67, c_0_57])).
% 0.20/0.41  cnf(c_0_75, negated_conjecture, (k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))!=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_40]), c_0_24]), c_0_36]), c_0_37]), c_0_41]), c_0_42]), c_0_43])).
% 0.20/0.41  cnf(c_0_76, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73])]), c_0_65]), c_0_74])).
% 0.20/0.41  cnf(c_0_77, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76])]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 78
% 0.20/0.41  # Proof object clause steps            : 37
% 0.20/0.41  # Proof object formula steps           : 41
% 0.20/0.41  # Proof object conjectures             : 6
% 0.20/0.41  # Proof object clause conjectures      : 3
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 22
% 0.20/0.41  # Proof object initial formulas used   : 20
% 0.20/0.41  # Proof object generating inferences   : 5
% 0.20/0.41  # Proof object simplifying inferences  : 90
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 21
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 28
% 0.20/0.41  # Removed in clause preprocessing      : 10
% 0.20/0.41  # Initial clauses in saturation        : 18
% 0.20/0.41  # Processed clauses                    : 166
% 0.20/0.41  # ...of these trivial                  : 5
% 0.20/0.41  # ...subsumed                          : 73
% 0.20/0.41  # ...remaining for further processing  : 88
% 0.20/0.41  # Other redundant clauses eliminated   : 57
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 3
% 0.20/0.41  # Backward-rewritten                   : 9
% 0.20/0.41  # Generated clauses                    : 1103
% 0.20/0.41  # ...of the previous two non-trivial   : 914
% 0.20/0.41  # Contextual simplify-reflections      : 1
% 0.20/0.41  # Paramodulations                      : 1041
% 0.20/0.41  # Factorizations                       : 6
% 0.20/0.41  # Equation resolutions                 : 57
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 54
% 0.20/0.41  #    Positive orientable unit clauses  : 14
% 0.20/0.41  #    Positive unorientable unit clauses: 3
% 0.20/0.41  #    Negative unit clauses             : 1
% 0.20/0.41  #    Non-unit-clauses                  : 36
% 0.20/0.41  # Current number of unprocessed clauses: 775
% 0.20/0.41  # ...number of literals in the above   : 3793
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 39
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 218
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 145
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 35
% 0.20/0.41  # Unit Clause-clause subsumption calls : 15
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 63
% 0.20/0.41  # BW rewrite match successes           : 52
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 15609
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.060 s
% 0.20/0.41  # System time              : 0.002 s
% 0.20/0.41  # Total time               : 0.062 s
% 0.20/0.41  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
