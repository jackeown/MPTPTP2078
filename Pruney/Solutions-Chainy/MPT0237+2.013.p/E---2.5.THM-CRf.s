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
% DateTime   : Thu Dec  3 10:39:20 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   91 (5243 expanded)
%              Number of clauses        :   46 (1971 expanded)
%              Number of leaves         :   22 (1628 expanded)
%              Depth                    :   10
%              Number of atoms          :  153 (5803 expanded)
%              Number of equality atoms :  104 (5057 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t32_zfmisc_1,conjecture,(
    ! [X1,X2] : k3_tarski(k2_tarski(k1_tarski(X1),k1_tarski(X2))) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).

fof(t17_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X1 != X2
     => r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

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

fof(t31_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(t29_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X1 != X2
     => k5_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k2_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

fof(l31_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k3_xboole_0(X2,k1_tarski(X1)) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(c_0_22,plain,(
    ! [X24,X25] : r1_xboole_0(k4_xboole_0(X24,X25),X25) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_23,plain,(
    ! [X18,X19] : k4_xboole_0(X18,X19) = k5_xboole_0(X18,k3_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_24,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_26,plain,(
    ! [X9] : k3_xboole_0(X9,X9) = X9 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_27,plain,(
    ! [X64,X65] : k3_tarski(k2_tarski(X64,X65)) = k2_xboole_0(X64,X65) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_28,plain,(
    ! [X42,X43] : k1_enumset1(X42,X42,X43) = k2_tarski(X42,X43) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_29,plain,(
    ! [X22,X23] : r1_tarski(k4_xboole_0(X22,X23),X22) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_30,plain,(
    ! [X10,X11,X13,X14,X15] :
      ( ( r1_xboole_0(X10,X11)
        | r2_hidden(esk1_2(X10,X11),k3_xboole_0(X10,X11)) )
      & ( ~ r2_hidden(X15,k3_xboole_0(X13,X14))
        | ~ r1_xboole_0(X13,X14) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_31,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_33,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_34,negated_conjecture,(
    ~ ! [X1,X2] : k3_tarski(k2_tarski(k1_tarski(X1),k1_tarski(X2))) = k2_tarski(X1,X2) ),
    inference(assume_negation,[status(cth)],[t32_zfmisc_1])).

fof(c_0_35,plain,(
    ! [X66,X67] :
      ( X66 = X67
      | r1_xboole_0(k1_tarski(X66),k1_tarski(X67)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_zfmisc_1])])).

fof(c_0_36,plain,(
    ! [X41] : k2_tarski(X41,X41) = k1_tarski(X41) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_37,plain,(
    ! [X44,X45,X46] : k2_enumset1(X44,X44,X45,X46) = k1_enumset1(X44,X45,X46) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_38,plain,(
    ! [X47,X48,X49,X50] : k3_enumset1(X47,X47,X48,X49,X50) = k2_enumset1(X47,X48,X49,X50) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_39,plain,(
    ! [X51,X52,X53,X54,X55] : k4_enumset1(X51,X51,X52,X53,X54,X55) = k3_enumset1(X51,X52,X53,X54,X55) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_40,plain,(
    ! [X56,X57,X58,X59,X60,X61] : k5_enumset1(X56,X56,X57,X58,X59,X60,X61) = k4_enumset1(X56,X57,X58,X59,X60,X61) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_41,plain,(
    ! [X70] : k3_tarski(k1_tarski(X70)) = X70 ),
    inference(variable_rename,[status(thm)],[t31_zfmisc_1])).

fof(c_0_42,plain,(
    ! [X28,X29] : k2_xboole_0(X28,X29) = k5_xboole_0(X28,k4_xboole_0(X29,X28)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_43,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_44,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_45,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_47,plain,
    ( r1_xboole_0(k5_xboole_0(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_49,plain,(
    ! [X16] :
      ( X16 = k1_xboole_0
      | r2_hidden(esk2_1(X16),X16) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_50,negated_conjecture,(
    k3_tarski(k2_tarski(k1_tarski(esk4_0),k1_tarski(esk5_0))) != k2_tarski(esk4_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_34])])])).

cnf(c_0_51,plain,
    ( X1 = X2
    | r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_52,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_53,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_54,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_55,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_56,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_57,plain,
    ( k3_tarski(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_59,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_60,plain,(
    ! [X20,X21] :
      ( ~ r1_tarski(X20,X21)
      | k3_xboole_0(X20,X21) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_61,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_45,c_0_25])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k5_xboole_0(X2,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_63,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_64,plain,(
    ! [X30,X31,X32,X33,X34,X35,X36,X37,X38,X39] :
      ( ( ~ r2_hidden(X34,X33)
        | X34 = X30
        | X34 = X31
        | X34 = X32
        | X33 != k1_enumset1(X30,X31,X32) )
      & ( X35 != X30
        | r2_hidden(X35,X33)
        | X33 != k1_enumset1(X30,X31,X32) )
      & ( X35 != X31
        | r2_hidden(X35,X33)
        | X33 != k1_enumset1(X30,X31,X32) )
      & ( X35 != X32
        | r2_hidden(X35,X33)
        | X33 != k1_enumset1(X30,X31,X32) )
      & ( esk3_4(X36,X37,X38,X39) != X36
        | ~ r2_hidden(esk3_4(X36,X37,X38,X39),X39)
        | X39 = k1_enumset1(X36,X37,X38) )
      & ( esk3_4(X36,X37,X38,X39) != X37
        | ~ r2_hidden(esk3_4(X36,X37,X38,X39),X39)
        | X39 = k1_enumset1(X36,X37,X38) )
      & ( esk3_4(X36,X37,X38,X39) != X38
        | ~ r2_hidden(esk3_4(X36,X37,X38,X39),X39)
        | X39 = k1_enumset1(X36,X37,X38) )
      & ( r2_hidden(esk3_4(X36,X37,X38,X39),X39)
        | esk3_4(X36,X37,X38,X39) = X36
        | esk3_4(X36,X37,X38,X39) = X37
        | esk3_4(X36,X37,X38,X39) = X38
        | X39 = k1_enumset1(X36,X37,X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_65,negated_conjecture,
    ( k3_tarski(k2_tarski(k1_tarski(esk4_0),k1_tarski(esk5_0))) != k2_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_66,plain,
    ( X1 = X2
    | r1_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52]),c_0_52]),c_0_44]),c_0_44]),c_0_53]),c_0_53]),c_0_54]),c_0_54]),c_0_55]),c_0_55]),c_0_56]),c_0_56])).

cnf(c_0_67,plain,
    ( k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_52]),c_0_44]),c_0_53]),c_0_54]),c_0_55]),c_0_56])).

cnf(c_0_68,plain,
    ( k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59]),c_0_25]),c_0_53]),c_0_54]),c_0_55]),c_0_56])).

cnf(c_0_69,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_70,plain,
    ( r1_tarski(k5_xboole_0(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_32])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

fof(c_0_72,plain,(
    ! [X68,X69] :
      ( X68 = X69
      | k5_xboole_0(k1_tarski(X68),k1_tarski(X69)) = k2_tarski(X68,X69) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_zfmisc_1])])).

fof(c_0_73,plain,(
    ! [X62,X63] :
      ( ~ r2_hidden(X62,X63)
      | k3_xboole_0(X63,k1_tarski(X62)) = k1_tarski(X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l31_zfmisc_1])])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_75,negated_conjecture,
    ( k3_tarski(k5_enumset1(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) != k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_52]),c_0_52]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_55]),c_0_55]),c_0_55]),c_0_55]),c_0_55]),c_0_55]),c_0_55]),c_0_56]),c_0_56]),c_0_56]),c_0_56]),c_0_56]),c_0_56]),c_0_56]),c_0_56])).

cnf(c_0_76,plain,
    ( X1 = X2
    | ~ r2_hidden(X3,k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_66])).

cnf(c_0_77,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68]),c_0_32])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_48]),c_0_71])).

cnf(c_0_79,plain,
    ( X1 = X2
    | k5_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_80,plain,
    ( k3_xboole_0(X2,k1_tarski(X1)) = k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_81,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X2,X2,X2,X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_53]),c_0_54]),c_0_55]),c_0_56])).

cnf(c_0_82,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))) != k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_68]),c_0_48])).

cnf(c_0_83,plain,
    ( k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2)) = k1_xboole_0
    | X1 = X2 ),
    inference(spm,[status(thm)],[c_0_76,c_0_63])).

cnf(c_0_84,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_85,plain,
    ( X1 = X2
    | k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2)) = k5_enumset1(X1,X1,X1,X1,X1,X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_52]),c_0_52]),c_0_44]),c_0_44]),c_0_44]),c_0_53]),c_0_53]),c_0_53]),c_0_54]),c_0_54]),c_0_54]),c_0_55]),c_0_55]),c_0_55]),c_0_56]),c_0_56]),c_0_56])).

cnf(c_0_86,plain,
    ( k3_xboole_0(X2,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = k5_enumset1(X1,X1,X1,X1,X1,X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_52]),c_0_52]),c_0_44]),c_0_44]),c_0_53]),c_0_53]),c_0_54]),c_0_54]),c_0_55]),c_0_55]),c_0_56]),c_0_56])).

cnf(c_0_87,plain,
    ( r2_hidden(X1,k5_enumset1(X1,X1,X1,X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_81])])).

cnf(c_0_88,negated_conjecture,
    ( esk5_0 = esk4_0 ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84]),c_0_85])).

cnf(c_0_89,plain,
    ( k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = k5_enumset1(X1,X1,X1,X1,X1,X1,X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_88]),c_0_88]),c_0_88]),c_0_88]),c_0_88]),c_0_88]),c_0_88]),c_0_88]),c_0_88]),c_0_88]),c_0_88]),c_0_88]),c_0_88]),c_0_88]),c_0_89]),c_0_78]),c_0_84]),c_0_88])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:15:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.50  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S032I
% 0.20/0.50  # and selection function SelectUnlessUniqMax.
% 0.20/0.50  #
% 0.20/0.50  # Preprocessing time       : 0.028 s
% 0.20/0.50  # Presaturation interreduction done
% 0.20/0.50  
% 0.20/0.50  # Proof found!
% 0.20/0.50  # SZS status Theorem
% 0.20/0.50  # SZS output start CNFRefutation
% 0.20/0.50  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.20/0.50  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.50  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.20/0.50  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.20/0.50  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.50  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.20/0.50  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.20/0.50  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.50  fof(t32_zfmisc_1, conjecture, ![X1, X2]:k3_tarski(k2_tarski(k1_tarski(X1),k1_tarski(X2)))=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 0.20/0.50  fof(t17_zfmisc_1, axiom, ![X1, X2]:(X1!=X2=>r1_xboole_0(k1_tarski(X1),k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 0.20/0.50  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.50  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.50  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.50  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.50  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.50  fof(t31_zfmisc_1, axiom, ![X1]:k3_tarski(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 0.20/0.50  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.20/0.50  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.20/0.50  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.50  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.20/0.50  fof(t29_zfmisc_1, axiom, ![X1, X2]:(X1!=X2=>k5_xboole_0(k1_tarski(X1),k1_tarski(X2))=k2_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 0.20/0.50  fof(l31_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k3_xboole_0(X2,k1_tarski(X1))=k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 0.20/0.50  fof(c_0_22, plain, ![X24, X25]:r1_xboole_0(k4_xboole_0(X24,X25),X25), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.20/0.50  fof(c_0_23, plain, ![X18, X19]:k4_xboole_0(X18,X19)=k5_xboole_0(X18,k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.50  cnf(c_0_24, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.50  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.50  fof(c_0_26, plain, ![X9]:k3_xboole_0(X9,X9)=X9, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.20/0.50  fof(c_0_27, plain, ![X64, X65]:k3_tarski(k2_tarski(X64,X65))=k2_xboole_0(X64,X65), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.20/0.50  fof(c_0_28, plain, ![X42, X43]:k1_enumset1(X42,X42,X43)=k2_tarski(X42,X43), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.50  fof(c_0_29, plain, ![X22, X23]:r1_tarski(k4_xboole_0(X22,X23),X22), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.20/0.50  fof(c_0_30, plain, ![X10, X11, X13, X14, X15]:((r1_xboole_0(X10,X11)|r2_hidden(esk1_2(X10,X11),k3_xboole_0(X10,X11)))&(~r2_hidden(X15,k3_xboole_0(X13,X14))|~r1_xboole_0(X13,X14))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.20/0.50  cnf(c_0_31, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.50  cnf(c_0_32, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.50  fof(c_0_33, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.50  fof(c_0_34, negated_conjecture, ~(![X1, X2]:k3_tarski(k2_tarski(k1_tarski(X1),k1_tarski(X2)))=k2_tarski(X1,X2)), inference(assume_negation,[status(cth)],[t32_zfmisc_1])).
% 0.20/0.50  fof(c_0_35, plain, ![X66, X67]:(X66=X67|r1_xboole_0(k1_tarski(X66),k1_tarski(X67))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_zfmisc_1])])).
% 0.20/0.50  fof(c_0_36, plain, ![X41]:k2_tarski(X41,X41)=k1_tarski(X41), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.50  fof(c_0_37, plain, ![X44, X45, X46]:k2_enumset1(X44,X44,X45,X46)=k1_enumset1(X44,X45,X46), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.50  fof(c_0_38, plain, ![X47, X48, X49, X50]:k3_enumset1(X47,X47,X48,X49,X50)=k2_enumset1(X47,X48,X49,X50), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.50  fof(c_0_39, plain, ![X51, X52, X53, X54, X55]:k4_enumset1(X51,X51,X52,X53,X54,X55)=k3_enumset1(X51,X52,X53,X54,X55), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.50  fof(c_0_40, plain, ![X56, X57, X58, X59, X60, X61]:k5_enumset1(X56,X56,X57,X58,X59,X60,X61)=k4_enumset1(X56,X57,X58,X59,X60,X61), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.50  fof(c_0_41, plain, ![X70]:k3_tarski(k1_tarski(X70))=X70, inference(variable_rename,[status(thm)],[t31_zfmisc_1])).
% 0.20/0.50  fof(c_0_42, plain, ![X28, X29]:k2_xboole_0(X28,X29)=k5_xboole_0(X28,k4_xboole_0(X29,X28)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.20/0.50  cnf(c_0_43, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.50  cnf(c_0_44, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.50  cnf(c_0_45, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.50  cnf(c_0_46, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.50  cnf(c_0_47, plain, (r1_xboole_0(k5_xboole_0(X1,X1),X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.50  cnf(c_0_48, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.50  fof(c_0_49, plain, ![X16]:(X16=k1_xboole_0|r2_hidden(esk2_1(X16),X16)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.20/0.50  fof(c_0_50, negated_conjecture, k3_tarski(k2_tarski(k1_tarski(esk4_0),k1_tarski(esk5_0)))!=k2_tarski(esk4_0,esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_34])])])).
% 0.20/0.50  cnf(c_0_51, plain, (X1=X2|r1_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.50  cnf(c_0_52, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.50  cnf(c_0_53, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.50  cnf(c_0_54, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.50  cnf(c_0_55, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.50  cnf(c_0_56, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.50  cnf(c_0_57, plain, (k3_tarski(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.50  cnf(c_0_58, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.50  cnf(c_0_59, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.50  fof(c_0_60, plain, ![X20, X21]:(~r1_tarski(X20,X21)|k3_xboole_0(X20,X21)=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.50  cnf(c_0_61, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_45, c_0_25])).
% 0.20/0.50  cnf(c_0_62, plain, (~r2_hidden(X1,k3_xboole_0(X2,k5_xboole_0(X2,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 0.20/0.50  cnf(c_0_63, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.50  fof(c_0_64, plain, ![X30, X31, X32, X33, X34, X35, X36, X37, X38, X39]:(((~r2_hidden(X34,X33)|(X34=X30|X34=X31|X34=X32)|X33!=k1_enumset1(X30,X31,X32))&(((X35!=X30|r2_hidden(X35,X33)|X33!=k1_enumset1(X30,X31,X32))&(X35!=X31|r2_hidden(X35,X33)|X33!=k1_enumset1(X30,X31,X32)))&(X35!=X32|r2_hidden(X35,X33)|X33!=k1_enumset1(X30,X31,X32))))&((((esk3_4(X36,X37,X38,X39)!=X36|~r2_hidden(esk3_4(X36,X37,X38,X39),X39)|X39=k1_enumset1(X36,X37,X38))&(esk3_4(X36,X37,X38,X39)!=X37|~r2_hidden(esk3_4(X36,X37,X38,X39),X39)|X39=k1_enumset1(X36,X37,X38)))&(esk3_4(X36,X37,X38,X39)!=X38|~r2_hidden(esk3_4(X36,X37,X38,X39),X39)|X39=k1_enumset1(X36,X37,X38)))&(r2_hidden(esk3_4(X36,X37,X38,X39),X39)|(esk3_4(X36,X37,X38,X39)=X36|esk3_4(X36,X37,X38,X39)=X37|esk3_4(X36,X37,X38,X39)=X38)|X39=k1_enumset1(X36,X37,X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.20/0.50  cnf(c_0_65, negated_conjecture, (k3_tarski(k2_tarski(k1_tarski(esk4_0),k1_tarski(esk5_0)))!=k2_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.50  cnf(c_0_66, plain, (X1=X2|r1_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52]), c_0_52]), c_0_44]), c_0_44]), c_0_53]), c_0_53]), c_0_54]), c_0_54]), c_0_55]), c_0_55]), c_0_56]), c_0_56])).
% 0.20/0.50  cnf(c_0_67, plain, (k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_52]), c_0_44]), c_0_53]), c_0_54]), c_0_55]), c_0_56])).
% 0.20/0.50  cnf(c_0_68, plain, (k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59]), c_0_25]), c_0_53]), c_0_54]), c_0_55]), c_0_56])).
% 0.20/0.50  cnf(c_0_69, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.50  cnf(c_0_70, plain, (r1_tarski(k5_xboole_0(X1,X1),X1)), inference(spm,[status(thm)],[c_0_61, c_0_32])).
% 0.20/0.50  cnf(c_0_71, plain, (k3_xboole_0(X1,k5_xboole_0(X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.50  fof(c_0_72, plain, ![X68, X69]:(X68=X69|k5_xboole_0(k1_tarski(X68),k1_tarski(X69))=k2_tarski(X68,X69)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_zfmisc_1])])).
% 0.20/0.50  fof(c_0_73, plain, ![X62, X63]:(~r2_hidden(X62,X63)|k3_xboole_0(X63,k1_tarski(X62))=k1_tarski(X62)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l31_zfmisc_1])])).
% 0.20/0.50  cnf(c_0_74, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.50  cnf(c_0_75, negated_conjecture, (k3_tarski(k5_enumset1(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))!=k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_52]), c_0_52]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_54]), c_0_54]), c_0_54]), c_0_54]), c_0_54]), c_0_54]), c_0_55]), c_0_55]), c_0_55]), c_0_55]), c_0_55]), c_0_55]), c_0_55]), c_0_56]), c_0_56]), c_0_56]), c_0_56]), c_0_56]), c_0_56]), c_0_56]), c_0_56])).
% 0.20/0.50  cnf(c_0_76, plain, (X1=X2|~r2_hidden(X3,k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2)))), inference(spm,[status(thm)],[c_0_46, c_0_66])).
% 0.20/0.50  cnf(c_0_77, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_68]), c_0_32])).
% 0.20/0.50  cnf(c_0_78, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_48]), c_0_71])).
% 0.20/0.50  cnf(c_0_79, plain, (X1=X2|k5_xboole_0(k1_tarski(X1),k1_tarski(X2))=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.20/0.50  cnf(c_0_80, plain, (k3_xboole_0(X2,k1_tarski(X1))=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.20/0.50  cnf(c_0_81, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X2,X2,X2,X2,X2,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_53]), c_0_54]), c_0_55]), c_0_56])).
% 0.20/0.50  cnf(c_0_82, negated_conjecture, (k5_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))))!=k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_68]), c_0_48])).
% 0.20/0.50  cnf(c_0_83, plain, (k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2))=k1_xboole_0|X1=X2), inference(spm,[status(thm)],[c_0_76, c_0_63])).
% 0.20/0.50  cnf(c_0_84, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_77, c_0_78])).
% 0.20/0.50  cnf(c_0_85, plain, (X1=X2|k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2))=k5_enumset1(X1,X1,X1,X1,X1,X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_52]), c_0_52]), c_0_44]), c_0_44]), c_0_44]), c_0_53]), c_0_53]), c_0_53]), c_0_54]), c_0_54]), c_0_54]), c_0_55]), c_0_55]), c_0_55]), c_0_56]), c_0_56]), c_0_56])).
% 0.20/0.50  cnf(c_0_86, plain, (k3_xboole_0(X2,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))=k5_enumset1(X1,X1,X1,X1,X1,X1,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_52]), c_0_52]), c_0_44]), c_0_44]), c_0_53]), c_0_53]), c_0_54]), c_0_54]), c_0_55]), c_0_55]), c_0_56]), c_0_56])).
% 0.20/0.50  cnf(c_0_87, plain, (r2_hidden(X1,k5_enumset1(X1,X1,X1,X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_81])])).
% 0.20/0.50  cnf(c_0_88, negated_conjecture, (esk5_0=esk4_0), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84]), c_0_85])).
% 0.20/0.50  cnf(c_0_89, plain, (k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))=k5_enumset1(X1,X1,X1,X1,X1,X1,X1)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.20/0.50  cnf(c_0_90, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_88]), c_0_88]), c_0_88]), c_0_88]), c_0_88]), c_0_88]), c_0_88]), c_0_88]), c_0_88]), c_0_88]), c_0_88]), c_0_88]), c_0_88]), c_0_88]), c_0_89]), c_0_78]), c_0_84]), c_0_88])]), ['proof']).
% 0.20/0.50  # SZS output end CNFRefutation
% 0.20/0.50  # Proof object total steps             : 91
% 0.20/0.50  # Proof object clause steps            : 46
% 0.20/0.50  # Proof object formula steps           : 45
% 0.20/0.50  # Proof object conjectures             : 8
% 0.20/0.50  # Proof object clause conjectures      : 5
% 0.20/0.50  # Proof object formula conjectures     : 3
% 0.20/0.50  # Proof object initial clauses used    : 22
% 0.20/0.50  # Proof object initial formulas used   : 22
% 0.20/0.50  # Proof object generating inferences   : 9
% 0.20/0.50  # Proof object simplifying inferences  : 123
% 0.20/0.50  # Training examples: 0 positive, 0 negative
% 0.20/0.50  # Parsed axioms                        : 23
% 0.20/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.50  # Initial clauses                      : 32
% 0.20/0.50  # Removed in clause preprocessing      : 8
% 0.20/0.50  # Initial clauses in saturation        : 24
% 0.20/0.50  # Processed clauses                    : 1435
% 0.20/0.50  # ...of these trivial                  : 85
% 0.20/0.50  # ...subsumed                          : 1079
% 0.20/0.50  # ...remaining for further processing  : 271
% 0.20/0.50  # Other redundant clauses eliminated   : 282
% 0.20/0.50  # Clauses deleted for lack of memory   : 0
% 0.20/0.50  # Backward-subsumed                    : 10
% 0.20/0.50  # Backward-rewritten                   : 16
% 0.20/0.50  # Generated clauses                    : 8452
% 0.20/0.50  # ...of the previous two non-trivial   : 5399
% 0.20/0.50  # Contextual simplify-reflections      : 1
% 0.20/0.50  # Paramodulations                      : 8104
% 0.20/0.50  # Factorizations                       : 69
% 0.20/0.50  # Equation resolutions                 : 282
% 0.20/0.50  # Propositional unsat checks           : 0
% 0.20/0.50  #    Propositional check models        : 0
% 0.20/0.50  #    Propositional check unsatisfiable : 0
% 0.20/0.50  #    Propositional clauses             : 0
% 0.20/0.50  #    Propositional clauses after purity: 0
% 0.20/0.50  #    Propositional unsat core size     : 0
% 0.20/0.50  #    Propositional preprocessing time  : 0.000
% 0.20/0.50  #    Propositional encoding time       : 0.000
% 0.20/0.50  #    Propositional solver time         : 0.000
% 0.20/0.50  #    Success case prop preproc time    : 0.000
% 0.20/0.50  #    Success case prop encoding time   : 0.000
% 0.20/0.50  #    Success case prop solver time     : 0.000
% 0.20/0.50  # Current number of processed clauses  : 217
% 0.20/0.50  #    Positive orientable unit clauses  : 57
% 0.20/0.50  #    Positive unorientable unit clauses: 3
% 0.20/0.50  #    Negative unit clauses             : 5
% 0.20/0.50  #    Non-unit-clauses                  : 152
% 0.20/0.50  # Current number of unprocessed clauses: 3955
% 0.20/0.50  # ...number of literals in the above   : 13802
% 0.20/0.50  # Current number of archived formulas  : 0
% 0.20/0.50  # Current number of archived clauses   : 58
% 0.20/0.50  # Clause-clause subsumption calls (NU) : 5222
% 0.20/0.50  # Rec. Clause-clause subsumption calls : 4693
% 0.20/0.50  # Non-unit clause-clause subsumptions  : 513
% 0.20/0.50  # Unit Clause-clause subsumption calls : 71
% 0.20/0.50  # Rewrite failures with RHS unbound    : 0
% 0.20/0.50  # BW rewrite match attempts            : 163
% 0.20/0.50  # BW rewrite match successes           : 25
% 0.20/0.50  # Condensation attempts                : 0
% 0.20/0.50  # Condensation successes               : 0
% 0.20/0.50  # Termbank termtop insertions          : 201456
% 0.20/0.50  
% 0.20/0.50  # -------------------------------------------------
% 0.20/0.50  # User time                : 0.153 s
% 0.20/0.50  # System time              : 0.006 s
% 0.20/0.50  # Total time               : 0.159 s
% 0.20/0.50  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
