%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:04 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 409 expanded)
%              Number of clauses        :   51 ( 173 expanded)
%              Number of leaves         :   14 ( 116 expanded)
%              Depth                    :   14
%              Number of atoms          :  156 ( 649 expanded)
%              Number of equality atoms :   76 ( 460 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t12_ordinal1,conjecture,(
    ! [X1,X2] :
      ( k1_ordinal1(X1) = k1_ordinal1(X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_ordinal1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(c_0_14,plain,(
    ! [X63,X64] : k3_tarski(k2_tarski(X63,X64)) = k2_xboole_0(X63,X64) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X54,X55] : k1_enumset1(X54,X54,X55) = k2_tarski(X54,X55) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X72] : k1_ordinal1(X72) = k2_xboole_0(X72,k1_tarski(X72)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_17,plain,(
    ! [X53] : k2_tarski(X53,X53) = k1_tarski(X53) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k1_ordinal1(X1) = k1_ordinal1(X2)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t12_ordinal1])).

fof(c_0_19,plain,(
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

fof(c_0_20,plain,(
    ! [X36,X37,X38] : k4_xboole_0(k4_xboole_0(X36,X37),X38) = k4_xboole_0(X36,k2_xboole_0(X37,X38)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_21,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,plain,(
    ! [X56,X57,X58] : k2_enumset1(X56,X56,X57,X58) = k1_enumset1(X56,X57,X58) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X59,X60,X61,X62] : k3_enumset1(X59,X59,X60,X61,X62) = k2_enumset1(X59,X60,X61,X62) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_25,plain,(
    ! [X73] : r2_hidden(X73,k1_ordinal1(X73)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

cnf(c_0_26,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_28,negated_conjecture,
    ( k1_ordinal1(esk4_0) = k1_ordinal1(esk5_0)
    & esk4_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( k1_ordinal1(esk4_0) = k1_ordinal1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_37,plain,(
    ! [X46,X47,X48,X49,X50,X51] :
      ( ( ~ r2_hidden(X48,X47)
        | X48 = X46
        | X47 != k1_tarski(X46) )
      & ( X49 != X46
        | r2_hidden(X49,X47)
        | X47 != k1_tarski(X46) )
      & ( ~ r2_hidden(esk3_2(X50,X51),X51)
        | esk3_2(X50,X51) != X50
        | X51 = k1_tarski(X50) )
      & ( r2_hidden(esk3_2(X50,X51),X51)
        | esk3_2(X50,X51) = X50
        | X51 = k1_tarski(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,k3_enumset1(X1,X1,X1,X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_22]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) = k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_35]),c_0_35]),c_0_22]),c_0_22]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_33]),c_0_33])).

fof(c_0_42,plain,(
    ! [X68,X69] :
      ( ( k4_xboole_0(X68,k1_tarski(X69)) != X68
        | ~ r2_hidden(X69,X68) )
      & ( r2_hidden(X69,X68)
        | k4_xboole_0(X68,k1_tarski(X69)) = X68 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,k4_xboole_0(k4_xboole_0(X4,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk4_0,k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(X2,k1_tarski(X1)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_27]),c_0_22]),c_0_32]),c_0_33])).

fof(c_0_49,plain,(
    ! [X16] : k2_xboole_0(X16,X16) = X16 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_50,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k4_xboole_0(k4_xboole_0(X1,esk5_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1)) = X2
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_27]),c_0_22]),c_0_32]),c_0_33])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_48])])).

cnf(c_0_54,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk5_0,k4_xboole_0(X1,esk5_0))
    | ~ r2_hidden(esk4_0,k4_xboole_0(X1,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2))
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_60,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_61,plain,
    ( X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_27]),c_0_22]),c_0_32]),c_0_33])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk5_0,k4_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0))
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_64,plain,
    ( k4_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_27]),c_0_22]),c_0_32]),c_0_33])).

cnf(c_0_65,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,esk4_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) = k4_xboole_0(k4_xboole_0(X1,esk5_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_41]),c_0_39])).

fof(c_0_67,plain,(
    ! [X5,X6] :
      ( ~ r2_hidden(X5,X6)
      | ~ r2_hidden(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_68,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( esk4_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_71,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,esk5_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) = k4_xboole_0(X1,esk4_0)
    | r2_hidden(esk4_0,k4_xboole_0(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_66])).

cnf(c_0_73,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk4_0,k4_xboole_0(X1,esk4_0))
    | ~ r2_hidden(esk5_0,k4_xboole_0(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( ~ r2_hidden(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk4_0,k4_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_58]),c_0_76])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_77])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_78]),c_0_70]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n011.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 11:15:12 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 3.13/3.34  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 3.13/3.34  # and selection function SelectNegativeLiterals.
% 3.13/3.34  #
% 3.13/3.34  # Preprocessing time       : 0.028 s
% 3.13/3.34  # Presaturation interreduction done
% 3.13/3.34  
% 3.13/3.34  # Proof found!
% 3.13/3.34  # SZS status Theorem
% 3.13/3.34  # SZS output start CNFRefutation
% 3.13/3.34  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.13/3.34  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.13/3.34  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 3.13/3.34  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.13/3.34  fof(t12_ordinal1, conjecture, ![X1, X2]:(k1_ordinal1(X1)=k1_ordinal1(X2)=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_ordinal1)).
% 3.13/3.34  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.13/3.34  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.13/3.34  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.13/3.34  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.13/3.34  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 3.13/3.34  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.13/3.34  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.13/3.34  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.13/3.34  fof(antisymmetry_r2_hidden, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 3.13/3.34  fof(c_0_14, plain, ![X63, X64]:k3_tarski(k2_tarski(X63,X64))=k2_xboole_0(X63,X64), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 3.13/3.34  fof(c_0_15, plain, ![X54, X55]:k1_enumset1(X54,X54,X55)=k2_tarski(X54,X55), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 3.13/3.34  fof(c_0_16, plain, ![X72]:k1_ordinal1(X72)=k2_xboole_0(X72,k1_tarski(X72)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 3.13/3.34  fof(c_0_17, plain, ![X53]:k2_tarski(X53,X53)=k1_tarski(X53), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 3.13/3.34  fof(c_0_18, negated_conjecture, ~(![X1, X2]:(k1_ordinal1(X1)=k1_ordinal1(X2)=>X1=X2)), inference(assume_negation,[status(cth)],[t12_ordinal1])).
% 3.13/3.34  fof(c_0_19, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k4_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k4_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 3.13/3.34  fof(c_0_20, plain, ![X36, X37, X38]:k4_xboole_0(k4_xboole_0(X36,X37),X38)=k4_xboole_0(X36,k2_xboole_0(X37,X38)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 3.13/3.34  cnf(c_0_21, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.13/3.34  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.13/3.34  fof(c_0_23, plain, ![X56, X57, X58]:k2_enumset1(X56,X56,X57,X58)=k1_enumset1(X56,X57,X58), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 3.13/3.34  fof(c_0_24, plain, ![X59, X60, X61, X62]:k3_enumset1(X59,X59,X60,X61,X62)=k2_enumset1(X59,X60,X61,X62), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 3.13/3.34  fof(c_0_25, plain, ![X73]:r2_hidden(X73,k1_ordinal1(X73)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 3.13/3.34  cnf(c_0_26, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.13/3.34  cnf(c_0_27, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.13/3.34  fof(c_0_28, negated_conjecture, (k1_ordinal1(esk4_0)=k1_ordinal1(esk5_0)&esk4_0!=esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 3.13/3.34  cnf(c_0_29, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.13/3.34  cnf(c_0_30, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.13/3.34  cnf(c_0_31, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 3.13/3.34  cnf(c_0_32, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.13/3.34  cnf(c_0_33, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 3.13/3.34  cnf(c_0_34, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 3.13/3.34  cnf(c_0_35, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 3.13/3.34  cnf(c_0_36, negated_conjecture, (k1_ordinal1(esk4_0)=k1_ordinal1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 3.13/3.34  fof(c_0_37, plain, ![X46, X47, X48, X49, X50, X51]:(((~r2_hidden(X48,X47)|X48=X46|X47!=k1_tarski(X46))&(X49!=X46|r2_hidden(X49,X47)|X47!=k1_tarski(X46)))&((~r2_hidden(esk3_2(X50,X51),X51)|esk3_2(X50,X51)!=X50|X51=k1_tarski(X50))&(r2_hidden(esk3_2(X50,X51),X51)|esk3_2(X50,X51)=X50|X51=k1_tarski(X50)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 3.13/3.34  cnf(c_0_38, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_29])).
% 3.13/3.34  cnf(c_0_39, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33])).
% 3.13/3.34  cnf(c_0_40, plain, (r2_hidden(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,k3_enumset1(X1,X1,X1,X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_22]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33])).
% 3.13/3.34  cnf(c_0_41, negated_conjecture, (k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))=k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_35]), c_0_35]), c_0_22]), c_0_22]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_33]), c_0_33])).
% 3.13/3.34  fof(c_0_42, plain, ![X68, X69]:((k4_xboole_0(X68,k1_tarski(X69))!=X68|~r2_hidden(X69,X68))&(r2_hidden(X69,X68)|k4_xboole_0(X68,k1_tarski(X69))=X68)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 3.13/3.34  cnf(c_0_43, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 3.13/3.34  cnf(c_0_44, plain, (~r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))|~r2_hidden(X1,k4_xboole_0(k4_xboole_0(X4,X2),X3))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 3.13/3.34  cnf(c_0_45, negated_conjecture, (r2_hidden(esk4_0,k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 3.13/3.34  cnf(c_0_46, plain, (r2_hidden(X1,X2)|k4_xboole_0(X2,k1_tarski(X1))=X2), inference(split_conjunct,[status(thm)],[c_0_42])).
% 3.13/3.34  cnf(c_0_47, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.13/3.34  cnf(c_0_48, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_27]), c_0_22]), c_0_32]), c_0_33])).
% 3.13/3.34  fof(c_0_49, plain, ![X16]:k2_xboole_0(X16,X16)=X16, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 3.13/3.34  cnf(c_0_50, negated_conjecture, (~r2_hidden(esk4_0,k4_xboole_0(k4_xboole_0(X1,esk5_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 3.13/3.34  cnf(c_0_51, plain, (k4_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1))=X2|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_27]), c_0_22]), c_0_32]), c_0_33])).
% 3.13/3.34  cnf(c_0_52, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_47])).
% 3.13/3.34  cnf(c_0_53, plain, (r2_hidden(X1,k3_enumset1(X1,X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_48])])).
% 3.13/3.34  cnf(c_0_54, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_49])).
% 3.13/3.34  cnf(c_0_55, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 3.13/3.34  cnf(c_0_56, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.13/3.34  cnf(c_0_57, negated_conjecture, (r2_hidden(esk5_0,k4_xboole_0(X1,esk5_0))|~r2_hidden(esk4_0,k4_xboole_0(X1,esk5_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 3.13/3.34  cnf(c_0_58, plain, (r2_hidden(X1,k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2))|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 3.13/3.34  cnf(c_0_59, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 3.13/3.34  cnf(c_0_60, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_31]), c_0_32]), c_0_33])).
% 3.13/3.34  cnf(c_0_61, plain, (X1=X3|X2!=k3_enumset1(X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_27]), c_0_22]), c_0_32]), c_0_33])).
% 3.13/3.34  cnf(c_0_62, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_56])).
% 3.13/3.34  cnf(c_0_63, negated_conjecture, (r2_hidden(esk5_0,k4_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0))|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 3.13/3.34  cnf(c_0_64, plain, (k4_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2))!=X1|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_27]), c_0_22]), c_0_32]), c_0_33])).
% 3.13/3.34  cnf(c_0_65, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_39, c_0_60])).
% 3.13/3.34  cnf(c_0_66, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,esk4_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))=k4_xboole_0(k4_xboole_0(X1,esk5_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_41]), c_0_39])).
% 3.13/3.34  fof(c_0_67, plain, ![X5, X6]:(~r2_hidden(X5,X6)|~r2_hidden(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).
% 3.13/3.34  cnf(c_0_68, plain, (X1=X2|~r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_61])).
% 3.13/3.34  cnf(c_0_69, negated_conjecture, (r2_hidden(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 3.13/3.34  cnf(c_0_70, negated_conjecture, (esk4_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 3.13/3.34  cnf(c_0_71, plain, (~r2_hidden(X1,k4_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1)))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 3.13/3.34  cnf(c_0_72, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,esk5_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))=k4_xboole_0(X1,esk4_0)|r2_hidden(esk4_0,k4_xboole_0(X1,esk4_0))), inference(spm,[status(thm)],[c_0_51, c_0_66])).
% 3.13/3.34  cnf(c_0_73, plain, (~r2_hidden(X1,X2)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 3.13/3.34  cnf(c_0_74, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])).
% 3.13/3.34  cnf(c_0_75, negated_conjecture, (r2_hidden(esk4_0,k4_xboole_0(X1,esk4_0))|~r2_hidden(esk5_0,k4_xboole_0(X1,esk4_0))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 3.13/3.34  cnf(c_0_76, negated_conjecture, (~r2_hidden(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 3.13/3.34  cnf(c_0_77, negated_conjecture, (r2_hidden(esk4_0,k4_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_58]), c_0_76])).
% 3.13/3.34  cnf(c_0_78, negated_conjecture, (r2_hidden(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_62, c_0_77])).
% 3.13/3.34  cnf(c_0_79, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_78]), c_0_70]), ['proof']).
% 3.13/3.34  # SZS output end CNFRefutation
% 3.13/3.34  # Proof object total steps             : 80
% 3.13/3.34  # Proof object clause steps            : 51
% 3.13/3.34  # Proof object formula steps           : 29
% 3.13/3.34  # Proof object conjectures             : 19
% 3.13/3.34  # Proof object clause conjectures      : 16
% 3.13/3.34  # Proof object formula conjectures     : 3
% 3.13/3.34  # Proof object initial clauses used    : 19
% 3.13/3.34  # Proof object initial formulas used   : 14
% 3.13/3.34  # Proof object generating inferences   : 17
% 3.13/3.34  # Proof object simplifying inferences  : 55
% 3.13/3.34  # Training examples: 0 positive, 0 negative
% 3.13/3.34  # Parsed axioms                        : 27
% 3.13/3.34  # Removed by relevancy pruning/SinE    : 0
% 3.13/3.34  # Initial clauses                      : 44
% 3.13/3.34  # Removed in clause preprocessing      : 9
% 3.13/3.34  # Initial clauses in saturation        : 35
% 3.13/3.34  # Processed clauses                    : 11212
% 3.13/3.34  # ...of these trivial                  : 475
% 3.13/3.34  # ...subsumed                          : 9274
% 3.13/3.34  # ...remaining for further processing  : 1463
% 3.13/3.34  # Other redundant clauses eliminated   : 2352
% 3.13/3.34  # Clauses deleted for lack of memory   : 0
% 3.13/3.34  # Backward-subsumed                    : 36
% 3.13/3.34  # Backward-rewritten                   : 211
% 3.13/3.34  # Generated clauses                    : 366398
% 3.13/3.34  # ...of the previous two non-trivial   : 309819
% 3.13/3.34  # Contextual simplify-reflections      : 6
% 3.13/3.34  # Paramodulations                      : 364009
% 3.13/3.34  # Factorizations                       : 34
% 3.13/3.34  # Equation resolutions                 : 2353
% 3.13/3.34  # Propositional unsat checks           : 0
% 3.13/3.34  #    Propositional check models        : 0
% 3.13/3.34  #    Propositional check unsatisfiable : 0
% 3.13/3.34  #    Propositional clauses             : 0
% 3.13/3.34  #    Propositional clauses after purity: 0
% 3.13/3.34  #    Propositional unsat core size     : 0
% 3.13/3.34  #    Propositional preprocessing time  : 0.000
% 3.13/3.34  #    Propositional encoding time       : 0.000
% 3.13/3.34  #    Propositional solver time         : 0.000
% 3.13/3.34  #    Success case prop preproc time    : 0.000
% 3.13/3.34  #    Success case prop encoding time   : 0.000
% 3.13/3.34  #    Success case prop solver time     : 0.000
% 3.13/3.34  # Current number of processed clauses  : 1172
% 3.13/3.34  #    Positive orientable unit clauses  : 153
% 3.13/3.34  #    Positive unorientable unit clauses: 0
% 3.13/3.34  #    Negative unit clauses             : 186
% 3.13/3.34  #    Non-unit-clauses                  : 833
% 3.13/3.34  # Current number of unprocessed clauses: 297559
% 3.13/3.34  # ...number of literals in the above   : 1204631
% 3.13/3.34  # Current number of archived formulas  : 0
% 3.13/3.34  # Current number of archived clauses   : 291
% 3.13/3.34  # Clause-clause subsumption calls (NU) : 56848
% 3.13/3.34  # Rec. Clause-clause subsumption calls : 41488
% 3.13/3.34  # Non-unit clause-clause subsumptions  : 1857
% 3.13/3.34  # Unit Clause-clause subsumption calls : 9615
% 3.13/3.34  # Rewrite failures with RHS unbound    : 0
% 3.13/3.34  # BW rewrite match attempts            : 857
% 3.13/3.34  # BW rewrite match successes           : 63
% 3.13/3.34  # Condensation attempts                : 0
% 3.13/3.34  # Condensation successes               : 0
% 3.13/3.34  # Termbank termtop insertions          : 8778083
% 3.13/3.36  
% 3.13/3.36  # -------------------------------------------------
% 3.13/3.36  # User time                : 2.849 s
% 3.13/3.36  # System time              : 0.131 s
% 3.13/3.36  # Total time               : 2.980 s
% 3.13/3.36  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
