%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:55 EST 2020

% Result     : Theorem 6.94s
% Output     : CNFRefutation 6.94s
% Verified   : 
% Statistics : Number of formulae       :  135 (8018 expanded)
%              Number of clauses        :  106 (3806 expanded)
%              Number of leaves         :   14 (2104 expanded)
%              Depth                    :   19
%              Number of atoms          :  244 (11868 expanded)
%              Number of equality atoms :  118 (6447 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t96_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).

fof(l97_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t125_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k4_xboole_0(X1,X2)) = k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(t131_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( X1 != X2
     => ( r1_xboole_0(k2_zfmisc_1(k1_tarski(X1),X3),k2_zfmisc_1(k1_tarski(X2),X4))
        & r1_xboole_0(k2_zfmisc_1(X3,k1_tarski(X1)),k2_zfmisc_1(X4,k1_tarski(X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t88_enumset1,axiom,(
    ! [X1,X2] : k4_enumset1(X1,X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_enumset1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(c_0_14,plain,(
    ! [X21] : k4_xboole_0(X21,k1_xboole_0) = X21 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_15,plain,(
    ! [X17,X18] : k4_xboole_0(X17,X18) = k5_xboole_0(X17,k3_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_16,plain,(
    ! [X22,X23] : r1_tarski(k4_xboole_0(X22,X23),k5_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t96_xboole_1])).

fof(c_0_17,plain,(
    ! [X15,X16] : r1_xboole_0(k3_xboole_0(X15,X16),k5_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[l97_xboole_1])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X7,X8] :
      ( ( ~ r1_xboole_0(X7,X8)
        | k3_xboole_0(X7,X8) = k1_xboole_0 )
      & ( k3_xboole_0(X7,X8) != k1_xboole_0
        | r1_xboole_0(X7,X8) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_22,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_24,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_25,plain,(
    ! [X19,X20] :
      ( ~ r1_tarski(X19,X20)
      | k3_xboole_0(X19,X20) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_26,plain,(
    ! [X9,X10,X12,X13,X14] :
      ( ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_xboole_0(X9,X10) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | r1_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | ~ r1_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_27,plain,(
    ! [X40,X41,X42] :
      ( k2_zfmisc_1(k4_xboole_0(X40,X41),X42) = k4_xboole_0(k2_zfmisc_1(X40,X42),k2_zfmisc_1(X41,X42))
      & k2_zfmisc_1(X42,k4_xboole_0(X40,X41)) = k4_xboole_0(k2_zfmisc_1(X42,X40),k2_zfmisc_1(X42,X41)) ) ),
    inference(variable_rename,[status(thm)],[t125_zfmisc_1])).

fof(c_0_28,plain,(
    ! [X36,X37,X38,X39] : k2_zfmisc_1(k3_xboole_0(X36,X37),k3_xboole_0(X38,X39)) = k3_xboole_0(k2_zfmisc_1(X36,X38),k2_zfmisc_1(X37,X39)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

cnf(c_0_29,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( r1_xboole_0(k3_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k2_zfmisc_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_23])).

cnf(c_0_38,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_22])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_40,plain,
    ( k3_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_29]),c_0_32])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_23,c_0_32])).

cnf(c_0_42,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_22])).

cnf(c_0_45,plain,
    ( k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_19]),c_0_19])).

cnf(c_0_46,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_47,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X3,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_32]),c_0_36])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(spm,[status(thm)],[c_0_33,c_0_37])).

cnf(c_0_49,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_32])).

cnf(c_0_50,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)))) = k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_52,plain,
    ( k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) = k5_xboole_0(k2_zfmisc_1(X1,X3),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_19]),c_0_19])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk1_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_43])).

cnf(c_0_54,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X2,X4))))
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,k5_xboole_0(X3,k3_xboole_0(X3,X4)))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_55,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,k3_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)))) = k2_zfmisc_1(k3_xboole_0(X1,X3),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_39])).

cnf(c_0_56,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
    | k3_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X3,X2)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_57,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k5_xboole_0(X1,k1_xboole_0),X3)) = k2_zfmisc_1(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_48])).

cnf(c_0_58,plain,
    ( r1_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_48])).

cnf(c_0_59,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_60,plain,
    ( k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X1)),X2) = k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X2))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_52])).

cnf(c_0_61,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1
    | r2_hidden(esk1_2(X1,k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_53])).

cnf(c_0_62,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_32])).

cnf(c_0_63,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(k3_xboole_0(X2,X2),k1_xboole_0)))
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,k5_xboole_0(X3,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_39])).

cnf(c_0_64,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X3,X2),k2_zfmisc_1(X1,X4)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_32]),c_0_36])).

cnf(c_0_65,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k5_xboole_0(X1,k1_xboole_0),X3))
    | k2_zfmisc_1(X1,k3_xboole_0(X3,X2)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,plain,
    ( k3_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_58])).

cnf(c_0_67,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_59]),c_0_39])])).

cnf(c_0_68,plain,
    ( k2_zfmisc_1(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(X1,X1))) = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_41])).

cnf(c_0_69,plain,
    ( k3_xboole_0(X1,X1) = X1
    | r2_hidden(esk1_2(X1,k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_61])).

cnf(c_0_70,plain,
    ( r1_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_38])).

cnf(c_0_71,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
    | k3_xboole_0(k2_zfmisc_1(X3,X2),k2_zfmisc_1(X1,X4)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_47])).

cnf(c_0_72,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = k1_xboole_0
    | r2_hidden(esk1_2(X1,k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_53])).

cnf(c_0_73,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,k1_xboole_0),k2_zfmisc_1(k3_xboole_0(X2,X2),X3)))
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,k5_xboole_0(X3,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_32]),c_0_64])).

cnf(c_0_74,plain,
    ( k5_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k1_xboole_0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_39])).

cnf(c_0_75,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_76,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,k5_xboole_0(k5_xboole_0(X2,k1_xboole_0),X2)),k2_zfmisc_1(k5_xboole_0(X1,k1_xboole_0),X2))
    | k2_zfmisc_1(X1,k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_77,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(sr,[status(thm)],[c_0_61,c_0_67])).

cnf(c_0_78,plain,
    ( k3_xboole_0(k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3),k3_xboole_0(k2_zfmisc_1(X1,X3),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_52]),c_0_32])).

cnf(c_0_79,plain,
    ( k2_zfmisc_1(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0)) = k2_zfmisc_1(k1_xboole_0,X1)
    | r2_hidden(esk1_2(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_53])).

cnf(c_0_80,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,k5_xboole_0(X2,k1_xboole_0))) = k2_zfmisc_1(k3_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_48])).

cnf(c_0_81,plain,
    ( k2_zfmisc_1(k1_xboole_0,k5_xboole_0(X1,X1)) = k2_zfmisc_1(k1_xboole_0,X1)
    | r2_hidden(esk1_2(X1,k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_82,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(k5_xboole_0(X1,X2),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_53])).

cnf(c_0_83,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,k3_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0))))
    | k2_zfmisc_1(k3_xboole_0(X3,X1),k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_55])).

cnf(c_0_84,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_72,c_0_67])).

cnf(c_0_85,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_2(X1,k1_xboole_0),k1_xboole_0)
    | r2_hidden(esk1_2(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_69])).

cnf(c_0_86,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))))
    | ~ r2_hidden(X1,k2_zfmisc_1(k3_xboole_0(X2,k3_xboole_0(X2,X2)),k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_55]),c_0_74])).

cnf(c_0_87,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(sr,[status(thm)],[c_0_69,c_0_67])).

fof(c_0_88,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( X1 != X2
       => ( r1_xboole_0(k2_zfmisc_1(k1_tarski(X1),X3),k2_zfmisc_1(k1_tarski(X2),X4))
          & r1_xboole_0(k2_zfmisc_1(X3,k1_tarski(X1)),k2_zfmisc_1(X4,k1_tarski(X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t131_zfmisc_1])).

cnf(c_0_89,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_75])).

cnf(c_0_90,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,k5_xboole_0(X2,X2)),k2_zfmisc_1(X1,X2))
    | k2_zfmisc_1(X1,k1_xboole_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77]),c_0_77])).

cnf(c_0_91,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0
    | r2_hidden(esk1_2(X1,X1),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_23]),c_0_47]),c_0_80]),c_0_47]),c_0_80]),c_0_47]),c_0_80]),c_0_39])).

cnf(c_0_92,plain,
    ( k2_zfmisc_1(k1_xboole_0,k5_xboole_0(X1,X1)) = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(sr,[status(thm)],[c_0_81,c_0_67])).

cnf(c_0_93,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_77]),c_0_67])).

cnf(c_0_94,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,k1_xboole_0))
    | k2_zfmisc_1(k3_xboole_0(X3,X1),k1_xboole_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_95,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_2(X1,X1),X1) ),
    inference(sr,[status(thm)],[c_0_85,c_0_67])).

cnf(c_0_96,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87]),c_0_87]),c_0_87]),c_0_87])])).

fof(c_0_97,negated_conjecture,
    ( esk3_0 != esk4_0
    & ( ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(esk3_0),esk5_0),k2_zfmisc_1(k1_tarski(esk4_0),esk6_0))
      | ~ r1_xboole_0(k2_zfmisc_1(esk5_0,k1_tarski(esk3_0)),k2_zfmisc_1(esk6_0,k1_tarski(esk4_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_88])])])).

fof(c_0_98,plain,(
    ! [X33] : k2_tarski(X33,X33) = k1_tarski(X33) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_99,plain,(
    ! [X34,X35] : k4_enumset1(X34,X34,X34,X34,X34,X35) = k2_tarski(X34,X35) ),
    inference(variable_rename,[status(thm)],[t88_enumset1])).

cnf(c_0_100,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X2,X4))
    | r2_hidden(esk1_2(X1,X3),X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_89])).

cnf(c_0_101,plain,
    ( r1_xboole_0(k2_zfmisc_1(k1_xboole_0,X1),k2_zfmisc_1(k1_xboole_0,X1)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_92]),c_0_67])).

cnf(c_0_102,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_93])).

cnf(c_0_103,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96])).

fof(c_0_104,plain,(
    ! [X24,X25,X26,X27,X28,X29,X30,X31] :
      ( ( ~ r2_hidden(X27,X26)
        | X27 = X24
        | X27 = X25
        | X26 != k2_tarski(X24,X25) )
      & ( X28 != X24
        | r2_hidden(X28,X26)
        | X26 != k2_tarski(X24,X25) )
      & ( X28 != X25
        | r2_hidden(X28,X26)
        | X26 != k2_tarski(X24,X25) )
      & ( esk2_3(X29,X30,X31) != X29
        | ~ r2_hidden(esk2_3(X29,X30,X31),X31)
        | X31 = k2_tarski(X29,X30) )
      & ( esk2_3(X29,X30,X31) != X30
        | ~ r2_hidden(esk2_3(X29,X30,X31),X31)
        | X31 = k2_tarski(X29,X30) )
      & ( r2_hidden(esk2_3(X29,X30,X31),X31)
        | esk2_3(X29,X30,X31) = X29
        | esk2_3(X29,X30,X31) = X30
        | X31 = k2_tarski(X29,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_105,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(esk3_0),esk5_0),k2_zfmisc_1(k1_tarski(esk4_0),esk6_0))
    | ~ r1_xboole_0(k2_zfmisc_1(esk5_0,k1_tarski(esk3_0)),k2_zfmisc_1(esk6_0,k1_tarski(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_106,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_107,plain,
    ( k4_enumset1(X1,X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_108,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))
    | k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X4,X3)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_100])).

cnf(c_0_109,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_101]),c_0_87])).

cnf(c_0_110,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) = k2_zfmisc_1(k3_xboole_0(X1,X3),k1_xboole_0)
    | r2_hidden(esk1_2(X2,X4),X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_89])).

cnf(c_0_111,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r2_hidden(esk1_2(X2,X2),X2) ),
    inference(spm,[status(thm)],[c_0_102,c_0_95])).

cnf(c_0_112,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_103])).

cnf(c_0_113,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X2,X4))
    | r2_hidden(esk1_2(X1,X3),X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_53])).

cnf(c_0_114,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_115,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(esk5_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k2_zfmisc_1(esk6_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))
    | ~ r1_xboole_0(k2_zfmisc_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk5_0),k2_zfmisc_1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_106]),c_0_106]),c_0_106]),c_0_106]),c_0_107]),c_0_107]),c_0_107]),c_0_107])).

cnf(c_0_116,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_109])])).

cnf(c_0_117,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))
    | k2_zfmisc_1(k3_xboole_0(X4,X3),k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_110])).

cnf(c_0_118,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_96])).

cnf(c_0_119,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))
    | k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X4,X3)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_113])).

cnf(c_0_120,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k4_enumset1(X3,X3,X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_114,c_0_107])).

cnf(c_0_121,negated_conjecture,
    ( r2_hidden(esk1_2(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)),k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))
    | ~ r1_xboole_0(k2_zfmisc_1(esk5_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k2_zfmisc_1(esk6_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_115,c_0_116])).

cnf(c_0_122,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_117,c_0_118])])).

cnf(c_0_123,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_109])])).

cnf(c_0_124,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k4_enumset1(X3,X3,X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_120])).

cnf(c_0_125,negated_conjecture,
    ( r2_hidden(esk1_2(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)),k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_126,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) = k2_zfmisc_1(k3_xboole_0(X1,X3),k1_xboole_0)
    | r2_hidden(esk1_2(X2,X4),X4) ),
    inference(spm,[status(thm)],[c_0_36,c_0_53])).

cnf(c_0_127,negated_conjecture,
    ( r2_hidden(esk1_2(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))
    | ~ r1_xboole_0(k2_zfmisc_1(esk5_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k2_zfmisc_1(esk6_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_115,c_0_123])).

cnf(c_0_128,negated_conjecture,
    ( esk1_2(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_124,c_0_125])).

cnf(c_0_129,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))
    | k2_zfmisc_1(k3_xboole_0(X4,X3),k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_126])).

cnf(c_0_130,negated_conjecture,
    ( r2_hidden(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))
    | ~ r1_xboole_0(k2_zfmisc_1(esk5_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k2_zfmisc_1(esk6_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_127,c_0_128])).

cnf(c_0_131,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_129,c_0_118])])).

cnf(c_0_132,negated_conjecture,
    ( r2_hidden(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_131]),c_0_128])])).

cnf(c_0_133,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_134,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_132]),c_0_133]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:41:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 6.94/7.12  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 6.94/7.12  # and selection function SelectNegativeLiterals.
% 6.94/7.12  #
% 6.94/7.12  # Preprocessing time       : 0.027 s
% 6.94/7.12  # Presaturation interreduction done
% 6.94/7.12  
% 6.94/7.12  # Proof found!
% 6.94/7.12  # SZS status Theorem
% 6.94/7.12  # SZS output start CNFRefutation
% 6.94/7.12  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 6.94/7.12  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.94/7.12  fof(t96_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_xboole_1)).
% 6.94/7.12  fof(l97_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 6.94/7.12  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.94/7.12  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.94/7.12  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.94/7.12  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.94/7.12  fof(t125_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k4_xboole_0(X1,X2))=k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 6.94/7.12  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 6.94/7.12  fof(t131_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(X1!=X2=>(r1_xboole_0(k2_zfmisc_1(k1_tarski(X1),X3),k2_zfmisc_1(k1_tarski(X2),X4))&r1_xboole_0(k2_zfmisc_1(X3,k1_tarski(X1)),k2_zfmisc_1(X4,k1_tarski(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t131_zfmisc_1)).
% 6.94/7.12  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.94/7.12  fof(t88_enumset1, axiom, ![X1, X2]:k4_enumset1(X1,X1,X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_enumset1)).
% 6.94/7.12  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 6.94/7.12  fof(c_0_14, plain, ![X21]:k4_xboole_0(X21,k1_xboole_0)=X21, inference(variable_rename,[status(thm)],[t3_boole])).
% 6.94/7.12  fof(c_0_15, plain, ![X17, X18]:k4_xboole_0(X17,X18)=k5_xboole_0(X17,k3_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 6.94/7.12  fof(c_0_16, plain, ![X22, X23]:r1_tarski(k4_xboole_0(X22,X23),k5_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t96_xboole_1])).
% 6.94/7.12  fof(c_0_17, plain, ![X15, X16]:r1_xboole_0(k3_xboole_0(X15,X16),k5_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[l97_xboole_1])).
% 6.94/7.12  cnf(c_0_18, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 6.94/7.12  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 6.94/7.12  cnf(c_0_20, plain, (r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 6.94/7.12  fof(c_0_21, plain, ![X7, X8]:((~r1_xboole_0(X7,X8)|k3_xboole_0(X7,X8)=k1_xboole_0)&(k3_xboole_0(X7,X8)!=k1_xboole_0|r1_xboole_0(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 6.94/7.12  cnf(c_0_22, plain, (r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 6.94/7.12  cnf(c_0_23, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 6.94/7.12  fof(c_0_24, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 6.94/7.12  fof(c_0_25, plain, ![X19, X20]:(~r1_tarski(X19,X20)|k3_xboole_0(X19,X20)=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 6.94/7.12  fof(c_0_26, plain, ![X9, X10, X12, X13, X14]:(((r2_hidden(esk1_2(X9,X10),X9)|r1_xboole_0(X9,X10))&(r2_hidden(esk1_2(X9,X10),X10)|r1_xboole_0(X9,X10)))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|~r1_xboole_0(X12,X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 6.94/7.12  fof(c_0_27, plain, ![X40, X41, X42]:(k2_zfmisc_1(k4_xboole_0(X40,X41),X42)=k4_xboole_0(k2_zfmisc_1(X40,X42),k2_zfmisc_1(X41,X42))&k2_zfmisc_1(X42,k4_xboole_0(X40,X41))=k4_xboole_0(k2_zfmisc_1(X42,X40),k2_zfmisc_1(X42,X41))), inference(variable_rename,[status(thm)],[t125_zfmisc_1])).
% 6.94/7.12  fof(c_0_28, plain, ![X36, X37, X38, X39]:k2_zfmisc_1(k3_xboole_0(X36,X37),k3_xboole_0(X38,X39))=k3_xboole_0(k2_zfmisc_1(X36,X38),k2_zfmisc_1(X37,X39)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 6.94/7.12  cnf(c_0_29, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_20, c_0_19])).
% 6.94/7.12  cnf(c_0_30, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 6.94/7.12  cnf(c_0_31, plain, (r1_xboole_0(k3_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 6.94/7.12  cnf(c_0_32, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 6.94/7.12  cnf(c_0_33, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 6.94/7.12  cnf(c_0_34, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 6.94/7.12  cnf(c_0_35, plain, (k2_zfmisc_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 6.94/7.12  cnf(c_0_36, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 6.94/7.12  cnf(c_0_37, plain, (r1_tarski(X1,k5_xboole_0(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_29, c_0_23])).
% 6.94/7.12  cnf(c_0_38, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_22])).
% 6.94/7.12  cnf(c_0_39, plain, (k3_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 6.94/7.12  cnf(c_0_40, plain, (k3_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_29]), c_0_32])).
% 6.94/7.12  cnf(c_0_41, plain, (k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_23, c_0_32])).
% 6.94/7.12  cnf(c_0_42, plain, (k2_zfmisc_1(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 6.94/7.12  cnf(c_0_43, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 6.94/7.12  cnf(c_0_44, plain, (~r2_hidden(X1,k5_xboole_0(X2,X3))|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_34, c_0_22])).
% 6.94/7.12  cnf(c_0_45, plain, (k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_19]), c_0_19])).
% 6.94/7.12  cnf(c_0_46, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 6.94/7.12  cnf(c_0_47, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X3,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_32]), c_0_36])).
% 6.94/7.12  cnf(c_0_48, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k1_xboole_0))=X1), inference(spm,[status(thm)],[c_0_33, c_0_37])).
% 6.94/7.12  cnf(c_0_49, plain, (r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_22, c_0_32])).
% 6.94/7.12  cnf(c_0_50, plain, (k3_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))))=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 6.94/7.12  cnf(c_0_51, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))))=k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 6.94/7.12  cnf(c_0_52, plain, (k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)=k5_xboole_0(k2_zfmisc_1(X1,X3),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_19]), c_0_19])).
% 6.94/7.12  cnf(c_0_53, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk1_2(X1,X2),X2)), inference(spm,[status(thm)],[c_0_30, c_0_43])).
% 6.94/7.12  cnf(c_0_54, plain, (~r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X2,X4))))|~r2_hidden(X1,k2_zfmisc_1(X2,k5_xboole_0(X3,k3_xboole_0(X3,X4))))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 6.94/7.12  cnf(c_0_55, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,k3_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0))))=k2_zfmisc_1(k3_xboole_0(X1,X3),k1_xboole_0)), inference(spm,[status(thm)],[c_0_36, c_0_39])).
% 6.94/7.12  cnf(c_0_56, plain, (r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))|k3_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X3,X2))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 6.94/7.12  cnf(c_0_57, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k5_xboole_0(X1,k1_xboole_0),X3))=k2_zfmisc_1(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_36, c_0_48])).
% 6.94/7.12  cnf(c_0_58, plain, (r1_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),X1))), inference(spm,[status(thm)],[c_0_49, c_0_48])).
% 6.94/7.12  cnf(c_0_59, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 6.94/7.12  cnf(c_0_60, plain, (k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X1)),X2)=k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X2)))), inference(spm,[status(thm)],[c_0_45, c_0_52])).
% 6.94/7.12  cnf(c_0_61, plain, (k5_xboole_0(X1,k1_xboole_0)=X1|r2_hidden(esk1_2(X1,k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_23, c_0_53])).
% 6.94/7.12  cnf(c_0_62, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X2,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_32])).
% 6.94/7.12  cnf(c_0_63, plain, (~r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(k3_xboole_0(X2,X2),k1_xboole_0)))|~r2_hidden(X1,k2_zfmisc_1(X2,k5_xboole_0(X3,k1_xboole_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_39])).
% 6.94/7.12  cnf(c_0_64, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=k3_xboole_0(k2_zfmisc_1(X3,X2),k2_zfmisc_1(X1,X4))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_32]), c_0_36])).
% 6.94/7.12  cnf(c_0_65, plain, (r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k5_xboole_0(X1,k1_xboole_0),X3))|k2_zfmisc_1(X1,k3_xboole_0(X3,X2))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 6.94/7.12  cnf(c_0_66, plain, (k3_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_58])).
% 6.94/7.12  cnf(c_0_67, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_59]), c_0_39])])).
% 6.94/7.12  cnf(c_0_68, plain, (k2_zfmisc_1(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(X1,X1)))=k2_zfmisc_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_60, c_0_41])).
% 6.94/7.12  cnf(c_0_69, plain, (k3_xboole_0(X1,X1)=X1|r2_hidden(esk1_2(X1,k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_48, c_0_61])).
% 6.94/7.12  cnf(c_0_70, plain, (r1_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_62, c_0_38])).
% 6.94/7.12  cnf(c_0_71, plain, (r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))|k3_xboole_0(k2_zfmisc_1(X3,X2),k2_zfmisc_1(X1,X4))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_62, c_0_47])).
% 6.94/7.12  cnf(c_0_72, plain, (k3_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=k1_xboole_0|r2_hidden(esk1_2(X1,k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_39, c_0_53])).
% 6.94/7.12  cnf(c_0_73, plain, (~r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,k1_xboole_0),k2_zfmisc_1(k3_xboole_0(X2,X2),X3)))|~r2_hidden(X1,k2_zfmisc_1(X2,k5_xboole_0(X3,k1_xboole_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_32]), c_0_64])).
% 6.94/7.12  cnf(c_0_74, plain, (k5_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k1_xboole_0)=k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_41, c_0_39])).
% 6.94/7.12  cnf(c_0_75, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 6.94/7.12  cnf(c_0_76, plain, (r1_xboole_0(k2_zfmisc_1(X1,k5_xboole_0(k5_xboole_0(X2,k1_xboole_0),X2)),k2_zfmisc_1(k5_xboole_0(X1,k1_xboole_0),X2))|k2_zfmisc_1(X1,k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 6.94/7.12  cnf(c_0_77, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(sr,[status(thm)],[c_0_61, c_0_67])).
% 6.94/7.12  cnf(c_0_78, plain, (k3_xboole_0(k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3),k3_xboole_0(k2_zfmisc_1(X1,X3),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_52]), c_0_32])).
% 6.94/7.12  cnf(c_0_79, plain, (k2_zfmisc_1(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0))=k2_zfmisc_1(k1_xboole_0,X1)|r2_hidden(esk1_2(X1,X1),X1)), inference(spm,[status(thm)],[c_0_68, c_0_53])).
% 6.94/7.12  cnf(c_0_80, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,k5_xboole_0(X2,k1_xboole_0)))=k2_zfmisc_1(k3_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_36, c_0_48])).
% 6.94/7.12  cnf(c_0_81, plain, (k2_zfmisc_1(k1_xboole_0,k5_xboole_0(X1,X1))=k2_zfmisc_1(k1_xboole_0,X1)|r2_hidden(esk1_2(X1,k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 6.94/7.12  cnf(c_0_82, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(k5_xboole_0(X1,X2),k1_xboole_0)), inference(spm,[status(thm)],[c_0_70, c_0_53])).
% 6.94/7.12  cnf(c_0_83, plain, (r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,k3_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0))))|k2_zfmisc_1(k3_xboole_0(X3,X1),k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_71, c_0_55])).
% 6.94/7.12  cnf(c_0_84, plain, (k3_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(sr,[status(thm)],[c_0_72, c_0_67])).
% 6.94/7.12  cnf(c_0_85, plain, (X1=k1_xboole_0|r2_hidden(esk1_2(X1,k1_xboole_0),k1_xboole_0)|r2_hidden(esk1_2(X1,X1),X1)), inference(spm,[status(thm)],[c_0_53, c_0_69])).
% 6.94/7.12  cnf(c_0_86, plain, (~r2_hidden(X1,k2_zfmisc_1(X2,k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))))|~r2_hidden(X1,k2_zfmisc_1(k3_xboole_0(X2,k3_xboole_0(X2,X2)),k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_55]), c_0_74])).
% 6.94/7.12  cnf(c_0_87, plain, (k3_xboole_0(X1,X1)=X1), inference(sr,[status(thm)],[c_0_69, c_0_67])).
% 6.94/7.12  fof(c_0_88, negated_conjecture, ~(![X1, X2, X3, X4]:(X1!=X2=>(r1_xboole_0(k2_zfmisc_1(k1_tarski(X1),X3),k2_zfmisc_1(k1_tarski(X2),X4))&r1_xboole_0(k2_zfmisc_1(X3,k1_tarski(X1)),k2_zfmisc_1(X4,k1_tarski(X2)))))), inference(assume_negation,[status(cth)],[t131_zfmisc_1])).
% 6.94/7.12  cnf(c_0_89, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk1_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_30, c_0_75])).
% 6.94/7.12  cnf(c_0_90, plain, (r1_xboole_0(k2_zfmisc_1(X1,k5_xboole_0(X2,X2)),k2_zfmisc_1(X1,X2))|k2_zfmisc_1(X1,k1_xboole_0)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77]), c_0_77])).
% 6.94/7.12  cnf(c_0_91, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0|r2_hidden(esk1_2(X1,X1),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_23]), c_0_47]), c_0_80]), c_0_47]), c_0_80]), c_0_47]), c_0_80]), c_0_39])).
% 6.94/7.12  cnf(c_0_92, plain, (k2_zfmisc_1(k1_xboole_0,k5_xboole_0(X1,X1))=k2_zfmisc_1(k1_xboole_0,X1)), inference(sr,[status(thm)],[c_0_81, c_0_67])).
% 6.94/7.12  cnf(c_0_93, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_77]), c_0_67])).
% 6.94/7.12  cnf(c_0_94, plain, (r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,k1_xboole_0))|k2_zfmisc_1(k3_xboole_0(X3,X1),k1_xboole_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_83, c_0_84])).
% 6.94/7.12  cnf(c_0_95, plain, (X1=k1_xboole_0|r2_hidden(esk1_2(X1,X1),X1)), inference(sr,[status(thm)],[c_0_85, c_0_67])).
% 6.94/7.12  cnf(c_0_96, plain, (~r2_hidden(X1,k2_zfmisc_1(X2,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_87]), c_0_87]), c_0_87]), c_0_87])])).
% 6.94/7.12  fof(c_0_97, negated_conjecture, (esk3_0!=esk4_0&(~r1_xboole_0(k2_zfmisc_1(k1_tarski(esk3_0),esk5_0),k2_zfmisc_1(k1_tarski(esk4_0),esk6_0))|~r1_xboole_0(k2_zfmisc_1(esk5_0,k1_tarski(esk3_0)),k2_zfmisc_1(esk6_0,k1_tarski(esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_88])])])).
% 6.94/7.12  fof(c_0_98, plain, ![X33]:k2_tarski(X33,X33)=k1_tarski(X33), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 6.94/7.12  fof(c_0_99, plain, ![X34, X35]:k4_enumset1(X34,X34,X34,X34,X34,X35)=k2_tarski(X34,X35), inference(variable_rename,[status(thm)],[t88_enumset1])).
% 6.94/7.12  cnf(c_0_100, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X2,X4))|r2_hidden(esk1_2(X1,X3),X1)), inference(spm,[status(thm)],[c_0_36, c_0_89])).
% 6.94/7.12  cnf(c_0_101, plain, (r1_xboole_0(k2_zfmisc_1(k1_xboole_0,X1),k2_zfmisc_1(k1_xboole_0,X1))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_92]), c_0_67])).
% 6.94/7.12  cnf(c_0_102, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_93])).
% 6.94/7.12  cnf(c_0_103, plain, (r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,k1_xboole_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_96])).
% 6.94/7.12  fof(c_0_104, plain, ![X24, X25, X26, X27, X28, X29, X30, X31]:(((~r2_hidden(X27,X26)|(X27=X24|X27=X25)|X26!=k2_tarski(X24,X25))&((X28!=X24|r2_hidden(X28,X26)|X26!=k2_tarski(X24,X25))&(X28!=X25|r2_hidden(X28,X26)|X26!=k2_tarski(X24,X25))))&(((esk2_3(X29,X30,X31)!=X29|~r2_hidden(esk2_3(X29,X30,X31),X31)|X31=k2_tarski(X29,X30))&(esk2_3(X29,X30,X31)!=X30|~r2_hidden(esk2_3(X29,X30,X31),X31)|X31=k2_tarski(X29,X30)))&(r2_hidden(esk2_3(X29,X30,X31),X31)|(esk2_3(X29,X30,X31)=X29|esk2_3(X29,X30,X31)=X30)|X31=k2_tarski(X29,X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 6.94/7.12  cnf(c_0_105, negated_conjecture, (~r1_xboole_0(k2_zfmisc_1(k1_tarski(esk3_0),esk5_0),k2_zfmisc_1(k1_tarski(esk4_0),esk6_0))|~r1_xboole_0(k2_zfmisc_1(esk5_0,k1_tarski(esk3_0)),k2_zfmisc_1(esk6_0,k1_tarski(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_97])).
% 6.94/7.12  cnf(c_0_106, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_98])).
% 6.94/7.12  cnf(c_0_107, plain, (k4_enumset1(X1,X1,X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_99])).
% 6.94/7.12  cnf(c_0_108, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))|k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X4,X3))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_100])).
% 6.94/7.12  cnf(c_0_109, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_101]), c_0_87])).
% 6.94/7.12  cnf(c_0_110, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=k2_zfmisc_1(k3_xboole_0(X1,X3),k1_xboole_0)|r2_hidden(esk1_2(X2,X4),X2)), inference(spm,[status(thm)],[c_0_36, c_0_89])).
% 6.94/7.12  cnf(c_0_111, plain, (k3_xboole_0(X1,X2)=X2|r2_hidden(esk1_2(X2,X2),X2)), inference(spm,[status(thm)],[c_0_102, c_0_95])).
% 6.94/7.12  cnf(c_0_112, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_103])).
% 6.94/7.12  cnf(c_0_113, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X2,X4))|r2_hidden(esk1_2(X1,X3),X3)), inference(spm,[status(thm)],[c_0_36, c_0_53])).
% 6.94/7.12  cnf(c_0_114, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_104])).
% 6.94/7.12  cnf(c_0_115, negated_conjecture, (~r1_xboole_0(k2_zfmisc_1(esk5_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k2_zfmisc_1(esk6_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))|~r1_xboole_0(k2_zfmisc_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk5_0),k2_zfmisc_1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105, c_0_106]), c_0_106]), c_0_106]), c_0_106]), c_0_107]), c_0_107]), c_0_107]), c_0_107])).
% 6.94/7.12  cnf(c_0_116, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_108, c_0_109])])).
% 6.94/7.12  cnf(c_0_117, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))|k2_zfmisc_1(k3_xboole_0(X4,X3),k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_71, c_0_110])).
% 6.94/7.12  cnf(c_0_118, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_96])).
% 6.94/7.12  cnf(c_0_119, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))|k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X4,X3))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_113])).
% 6.94/7.12  cnf(c_0_120, plain, (X1=X4|X1=X3|X2!=k4_enumset1(X3,X3,X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_114, c_0_107])).
% 6.94/7.12  cnf(c_0_121, negated_conjecture, (r2_hidden(esk1_2(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)),k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))|~r1_xboole_0(k2_zfmisc_1(esk5_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k2_zfmisc_1(esk6_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))), inference(spm,[status(thm)],[c_0_115, c_0_116])).
% 6.94/7.12  cnf(c_0_122, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_117, c_0_118])])).
% 6.94/7.12  cnf(c_0_123, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_119, c_0_109])])).
% 6.94/7.12  cnf(c_0_124, plain, (X1=X2|X1=X3|~r2_hidden(X1,k4_enumset1(X3,X3,X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_120])).
% 6.94/7.12  cnf(c_0_125, negated_conjecture, (r2_hidden(esk1_2(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)),k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_121, c_0_122])).
% 6.94/7.12  cnf(c_0_126, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=k2_zfmisc_1(k3_xboole_0(X1,X3),k1_xboole_0)|r2_hidden(esk1_2(X2,X4),X4)), inference(spm,[status(thm)],[c_0_36, c_0_53])).
% 6.94/7.12  cnf(c_0_127, negated_conjecture, (r2_hidden(esk1_2(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))|~r1_xboole_0(k2_zfmisc_1(esk5_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k2_zfmisc_1(esk6_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))), inference(spm,[status(thm)],[c_0_115, c_0_123])).
% 6.94/7.12  cnf(c_0_128, negated_conjecture, (esk1_2(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))=esk3_0), inference(spm,[status(thm)],[c_0_124, c_0_125])).
% 6.94/7.12  cnf(c_0_129, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))|k2_zfmisc_1(k3_xboole_0(X4,X3),k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_71, c_0_126])).
% 6.94/7.12  cnf(c_0_130, negated_conjecture, (r2_hidden(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))|~r1_xboole_0(k2_zfmisc_1(esk5_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k2_zfmisc_1(esk6_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))), inference(rw,[status(thm)],[c_0_127, c_0_128])).
% 6.94/7.12  cnf(c_0_131, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_129, c_0_118])])).
% 6.94/7.12  cnf(c_0_132, negated_conjecture, (r2_hidden(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_131]), c_0_128])])).
% 6.94/7.12  cnf(c_0_133, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_97])).
% 6.94/7.12  cnf(c_0_134, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_132]), c_0_133]), ['proof']).
% 6.94/7.12  # SZS output end CNFRefutation
% 6.94/7.12  # Proof object total steps             : 135
% 6.94/7.12  # Proof object clause steps            : 106
% 6.94/7.12  # Proof object formula steps           : 29
% 6.94/7.12  # Proof object conjectures             : 13
% 6.94/7.12  # Proof object clause conjectures      : 10
% 6.94/7.12  # Proof object formula conjectures     : 3
% 6.94/7.12  # Proof object initial clauses used    : 19
% 6.94/7.12  # Proof object initial formulas used   : 14
% 6.94/7.12  # Proof object generating inferences   : 67
% 6.94/7.12  # Proof object simplifying inferences  : 65
% 6.94/7.12  # Training examples: 0 positive, 0 negative
% 6.94/7.12  # Parsed axioms                        : 15
% 6.94/7.12  # Removed by relevancy pruning/SinE    : 0
% 6.94/7.12  # Initial clauses                      : 25
% 6.94/7.12  # Removed in clause preprocessing      : 3
% 6.94/7.12  # Initial clauses in saturation        : 22
% 6.94/7.12  # Processed clauses                    : 19505
% 6.94/7.12  # ...of these trivial                  : 696
% 6.94/7.12  # ...subsumed                          : 15472
% 6.94/7.12  # ...remaining for further processing  : 3337
% 6.94/7.12  # Other redundant clauses eliminated   : 2802
% 6.94/7.12  # Clauses deleted for lack of memory   : 0
% 6.94/7.12  # Backward-subsumed                    : 283
% 6.94/7.12  # Backward-rewritten                   : 2221
% 6.94/7.12  # Generated clauses                    : 787877
% 6.94/7.12  # ...of the previous two non-trivial   : 755722
% 6.94/7.12  # Contextual simplify-reflections      : 8
% 6.94/7.12  # Paramodulations                      : 784807
% 6.94/7.12  # Factorizations                       : 202
% 6.94/7.12  # Equation resolutions                 : 2802
% 6.94/7.12  # Propositional unsat checks           : 0
% 6.94/7.12  #    Propositional check models        : 0
% 6.94/7.12  #    Propositional check unsatisfiable : 0
% 6.94/7.12  #    Propositional clauses             : 0
% 6.94/7.12  #    Propositional clauses after purity: 0
% 6.94/7.12  #    Propositional unsat core size     : 0
% 6.94/7.12  #    Propositional preprocessing time  : 0.000
% 6.94/7.12  #    Propositional encoding time       : 0.000
% 6.94/7.12  #    Propositional solver time         : 0.000
% 6.94/7.12  #    Success case prop preproc time    : 0.000
% 6.94/7.12  #    Success case prop encoding time   : 0.000
% 6.94/7.12  #    Success case prop solver time     : 0.000
% 6.94/7.12  # Current number of processed clauses  : 740
% 6.94/7.12  #    Positive orientable unit clauses  : 93
% 6.94/7.12  #    Positive unorientable unit clauses: 4
% 6.94/7.12  #    Negative unit clauses             : 2
% 6.94/7.12  #    Non-unit-clauses                  : 641
% 6.94/7.12  # Current number of unprocessed clauses: 734837
% 6.94/7.12  # ...number of literals in the above   : 3360136
% 6.94/7.12  # Current number of archived formulas  : 0
% 6.94/7.12  # Current number of archived clauses   : 2597
% 6.94/7.12  # Clause-clause subsumption calls (NU) : 2146566
% 6.94/7.12  # Rec. Clause-clause subsumption calls : 1333817
% 6.94/7.12  # Non-unit clause-clause subsumptions  : 14046
% 6.94/7.12  # Unit Clause-clause subsumption calls : 16395
% 6.94/7.12  # Rewrite failures with RHS unbound    : 0
% 6.94/7.12  # BW rewrite match attempts            : 875
% 6.94/7.12  # BW rewrite match successes           : 347
% 6.94/7.12  # Condensation attempts                : 0
% 6.94/7.12  # Condensation successes               : 0
% 6.94/7.12  # Termbank termtop insertions          : 31653673
% 6.94/7.15  
% 6.94/7.15  # -------------------------------------------------
% 6.94/7.15  # User time                : 6.507 s
% 6.94/7.15  # System time              : 0.299 s
% 6.94/7.15  # Total time               : 6.806 s
% 6.94/7.15  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
