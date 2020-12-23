%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:56 EST 2020

% Result     : Theorem 20.81s
% Output     : CNFRefutation 20.81s
% Verified   : 
% Statistics : Number of formulae       :  131 (13808 expanded)
%              Number of clauses        :   88 (5499 expanded)
%              Number of leaves         :   21 (4122 expanded)
%              Depth                    :   21
%              Number of atoms          :  275 (16357 expanded)
%              Number of equality atoms :  192 (15360 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   2 average)

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

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

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

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(c_0_21,plain,(
    ! [X72,X73] : k3_tarski(k2_tarski(X72,X73)) = k2_xboole_0(X72,X73) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_22,plain,(
    ! [X43,X44] : k1_enumset1(X43,X43,X44) = k2_tarski(X43,X44) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_xboole_0
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t43_zfmisc_1])).

fof(c_0_24,plain,(
    ! [X27,X28,X29] : k5_xboole_0(k5_xboole_0(X27,X28),X29) = k5_xboole_0(X27,k5_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_25,plain,(
    ! [X30] : k5_xboole_0(X30,X30) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_26,plain,(
    ! [X25,X26] : r1_tarski(X25,k2_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_27,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X45,X46,X47] : k2_enumset1(X45,X45,X46,X47) = k1_enumset1(X45,X46,X47) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_30,plain,(
    ! [X48,X49,X50,X51] : k3_enumset1(X48,X48,X49,X50,X51) = k2_enumset1(X48,X49,X50,X51) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_31,plain,(
    ! [X52,X53,X54,X55,X56] : k4_enumset1(X52,X52,X53,X54,X55,X56) = k3_enumset1(X52,X53,X54,X55,X56) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_32,plain,(
    ! [X57,X58,X59,X60,X61,X62] : k5_enumset1(X57,X57,X58,X59,X60,X61,X62) = k4_enumset1(X57,X58,X59,X60,X61,X62) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_33,plain,(
    ! [X63,X64,X65,X66,X67,X68,X69] : k6_enumset1(X63,X63,X64,X65,X66,X67,X68,X69) = k5_enumset1(X63,X64,X65,X66,X67,X68,X69) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_34,plain,(
    ! [X31,X32] : k2_xboole_0(X31,X32) = k5_xboole_0(X31,k4_xboole_0(X32,X31)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_35,plain,(
    ! [X19,X20] : k4_xboole_0(X19,X20) = k5_xboole_0(X19,k3_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_36,negated_conjecture,
    ( k1_tarski(esk4_0) = k2_xboole_0(esk5_0,esk6_0)
    & ( esk5_0 != k1_tarski(esk4_0)
      | esk6_0 != k1_tarski(esk4_0) )
    & ( esk5_0 != k1_xboole_0
      | esk6_0 != k1_tarski(esk4_0) )
    & ( esk5_0 != k1_tarski(esk4_0)
      | esk6_0 != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

fof(c_0_37,plain,(
    ! [X42] : k2_tarski(X42,X42) = k1_tarski(X42) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_38,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_40,plain,(
    ! [X24] : k5_xboole_0(X24,k1_xboole_0) = X24 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_43,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_45,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_48,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_50,negated_conjecture,
    ( k1_tarski(esk4_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_51,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_52,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_53,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_54,plain,(
    ! [X70,X71] :
      ( ( ~ r1_tarski(X70,k1_tarski(X71))
        | X70 = k1_xboole_0
        | X70 = k1_tarski(X71) )
      & ( X70 != k1_xboole_0
        | r1_tarski(X70,k1_tarski(X71)) )
      & ( X70 != k1_tarski(X71)
        | r1_tarski(X70,k1_tarski(X71)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_56,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_42]),c_0_49]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51]),c_0_28]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_47]),c_0_47])).

cnf(c_0_58,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_39]),c_0_53])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,k1_tarski(X2))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,esk5_0))) = k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_57,c_0_56])).

cnf(c_0_63,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[c_0_52,c_0_58])).

cnf(c_0_64,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_38])).

fof(c_0_65,plain,(
    ! [X21,X22] :
      ( ~ r1_tarski(X21,X22)
      | k2_xboole_0(X21,X22) = X22 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
    | X1 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_51]),c_0_51]),c_0_28]),c_0_28]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_47]),c_0_47])).

cnf(c_0_67,plain,
    ( X1 = k1_xboole_0
    | X1 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_51]),c_0_51]),c_0_28]),c_0_28]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_47]),c_0_47])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(esk5_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_53])).

cnf(c_0_70,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_71,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = esk5_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( k5_xboole_0(esk5_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) = k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_62])).

cnf(c_0_74,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X1))) = k5_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_69,c_0_38])).

cnf(c_0_75,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_76,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( k5_xboole_0(esk5_0,k5_xboole_0(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),X1)) = k5_xboole_0(esk6_0,k5_xboole_0(k3_xboole_0(esk6_0,esk5_0),X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_73]),c_0_38])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))))) = k5_xboole_0(X3,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_56]),c_0_38])).

cnf(c_0_79,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk5_0) = esk5_0
    | esk5_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_56]),c_0_63])).

cnf(c_0_80,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_69])).

fof(c_0_81,plain,(
    ! [X8,X9,X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X11,X10)
        | r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X10 != k2_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X12,X8)
        | r2_hidden(X12,X10)
        | X10 != k2_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X12,X9)
        | r2_hidden(X12,X10)
        | X10 != k2_xboole_0(X8,X9) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X13)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X14)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k2_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X15)
        | r2_hidden(esk1_3(X13,X14,X15),X13)
        | r2_hidden(esk1_3(X13,X14,X15),X14)
        | X15 = k2_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_82,negated_conjecture,
    ( esk5_0 != k1_tarski(esk4_0)
    | esk6_0 != k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_83,negated_conjecture,
    ( k5_xboole_0(esk6_0,k5_xboole_0(k3_xboole_0(esk6_0,esk5_0),X1)) = X1
    | esk5_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_72]),c_0_63])).

cnf(c_0_84,negated_conjecture,
    ( k5_xboole_0(X1,k3_xboole_0(esk5_0,esk5_0)) = k5_xboole_0(X1,esk5_0)
    | esk5_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_56]),c_0_63]),c_0_63])).

cnf(c_0_85,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_80])).

cnf(c_0_86,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_87,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

fof(c_0_88,plain,(
    ! [X33,X34,X35,X36,X37,X38,X39,X40] :
      ( ( ~ r2_hidden(X36,X35)
        | X36 = X33
        | X36 = X34
        | X35 != k2_tarski(X33,X34) )
      & ( X37 != X33
        | r2_hidden(X37,X35)
        | X35 != k2_tarski(X33,X34) )
      & ( X37 != X34
        | r2_hidden(X37,X35)
        | X35 != k2_tarski(X33,X34) )
      & ( esk3_3(X38,X39,X40) != X38
        | ~ r2_hidden(esk3_3(X38,X39,X40),X40)
        | X40 = k2_tarski(X38,X39) )
      & ( esk3_3(X38,X39,X40) != X39
        | ~ r2_hidden(esk3_3(X38,X39,X40),X40)
        | X40 = k2_tarski(X38,X39) )
      & ( r2_hidden(esk3_3(X38,X39,X40),X40)
        | esk3_3(X38,X39,X40) = X38
        | esk3_3(X38,X39,X40) = X39
        | X40 = k2_tarski(X38,X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_89,negated_conjecture,
    ( esk5_0 != k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)
    | esk6_0 != k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_51]),c_0_51]),c_0_28]),c_0_28]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_47]),c_0_47])).

cnf(c_0_90,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k3_xboole_0(esk5_0,esk5_0)
    | esk5_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_80]),c_0_85]),c_0_80]),c_0_62])).

cnf(c_0_91,plain,
    ( X3 = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_92,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])).

fof(c_0_93,plain,(
    ! [X17] :
      ( X17 = k1_xboole_0
      | r2_hidden(esk2_1(X17),X17) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_94,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_95,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | k3_xboole_0(esk5_0,esk5_0) != esk6_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_79])).

cnf(c_0_96,plain,
    ( X1 = k3_xboole_0(X2,X2)
    | r2_hidden(esk1_3(X2,X2,X1),X2)
    | r2_hidden(esk1_3(X2,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_91]),c_0_56]),c_0_63])).

cnf(c_0_97,plain,
    ( r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_92])).

cnf(c_0_98,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_99,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_28]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_100,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(esk1_3(esk5_0,esk5_0,esk6_0),esk6_0)
    | r2_hidden(esk1_3(esk5_0,esk5_0,esk6_0),esk5_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96])])).

cnf(c_0_101,negated_conjecture,
    ( k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,esk5_0)) = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_72]),c_0_39])).

cnf(c_0_102,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_103,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_104,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_99])).

cnf(c_0_105,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(esk1_3(esk5_0,esk5_0,esk6_0),k5_xboole_0(X1,k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,X1))))
    | r2_hidden(esk1_3(esk5_0,esk5_0,esk6_0),esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_100]),c_0_56])).

cnf(c_0_106,negated_conjecture,
    ( k3_xboole_0(esk6_0,esk5_0) = esk6_0
    | esk5_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_101]),c_0_53])).

cnf(c_0_107,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_28]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_108,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_103,c_0_56])).

cnf(c_0_109,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_110,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | X1 = esk4_0
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_104,c_0_72])).

cnf(c_0_111,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(esk1_3(esk5_0,esk5_0,esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_39]),c_0_53])])).

cnf(c_0_112,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_107])])).

cnf(c_0_113,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | r2_hidden(esk2_1(esk6_0),esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_106]),c_0_39]),c_0_53])).

cnf(c_0_114,plain,
    ( X3 = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_115,negated_conjecture,
    ( esk1_3(esk5_0,esk5_0,esk6_0) = esk4_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_116,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_112,c_0_72])).

cnf(c_0_117,negated_conjecture,
    ( esk5_0 != k1_tarski(esk4_0)
    | esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_118,negated_conjecture,
    ( esk2_1(esk6_0) = esk4_0
    | esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_110,c_0_113])).

cnf(c_0_119,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | ~ r2_hidden(esk4_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_56]),c_0_63]),c_0_116]),c_0_95])).

cnf(c_0_120,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | esk6_0 != k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_121,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | esk5_0 != k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117,c_0_51]),c_0_28]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_122,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_118]),c_0_119])).

cnf(c_0_123,negated_conjecture,
    ( k5_xboole_0(esk6_0,k5_xboole_0(k3_xboole_0(esk6_0,esk5_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) = esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_73]),c_0_80]),c_0_38])).

fof(c_0_124,plain,(
    ! [X23] : k3_xboole_0(X23,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_125,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | esk6_0 != k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_120,c_0_51]),c_0_28]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_126,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_72])).

cnf(c_0_127,negated_conjecture,
    ( k5_xboole_0(k3_xboole_0(esk6_0,esk5_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) = k5_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_123]),c_0_80])).

cnf(c_0_128,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_124])).

cnf(c_0_129,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_125,c_0_126])])).

cnf(c_0_130,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_127,c_0_126]),c_0_128]),c_0_58]),c_0_126]),c_0_58]),c_0_129]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 20.81/21.01  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 20.81/21.01  # and selection function GSelectMinInfpos.
% 20.81/21.01  #
% 20.81/21.01  # Preprocessing time       : 0.028 s
% 20.81/21.01  # Presaturation interreduction done
% 20.81/21.01  
% 20.81/21.01  # Proof found!
% 20.81/21.01  # SZS status Theorem
% 20.81/21.01  # SZS output start CNFRefutation
% 20.81/21.01  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 20.81/21.01  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 20.81/21.01  fof(t43_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 20.81/21.01  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 20.81/21.01  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 20.81/21.01  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 20.81/21.01  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 20.81/21.01  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 20.81/21.01  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 20.81/21.01  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 20.81/21.01  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 20.81/21.01  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 20.81/21.01  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 20.81/21.01  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 20.81/21.01  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 20.81/21.01  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 20.81/21.01  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 20.81/21.01  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 20.81/21.01  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 20.81/21.01  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 20.81/21.01  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 20.81/21.01  fof(c_0_21, plain, ![X72, X73]:k3_tarski(k2_tarski(X72,X73))=k2_xboole_0(X72,X73), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 20.81/21.01  fof(c_0_22, plain, ![X43, X44]:k1_enumset1(X43,X43,X44)=k2_tarski(X43,X44), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 20.81/21.01  fof(c_0_23, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0))))), inference(assume_negation,[status(cth)],[t43_zfmisc_1])).
% 20.81/21.01  fof(c_0_24, plain, ![X27, X28, X29]:k5_xboole_0(k5_xboole_0(X27,X28),X29)=k5_xboole_0(X27,k5_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 20.81/21.01  fof(c_0_25, plain, ![X30]:k5_xboole_0(X30,X30)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 20.81/21.01  fof(c_0_26, plain, ![X25, X26]:r1_tarski(X25,k2_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 20.81/21.01  cnf(c_0_27, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 20.81/21.01  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 20.81/21.01  fof(c_0_29, plain, ![X45, X46, X47]:k2_enumset1(X45,X45,X46,X47)=k1_enumset1(X45,X46,X47), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 20.81/21.01  fof(c_0_30, plain, ![X48, X49, X50, X51]:k3_enumset1(X48,X48,X49,X50,X51)=k2_enumset1(X48,X49,X50,X51), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 20.81/21.01  fof(c_0_31, plain, ![X52, X53, X54, X55, X56]:k4_enumset1(X52,X52,X53,X54,X55,X56)=k3_enumset1(X52,X53,X54,X55,X56), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 20.81/21.01  fof(c_0_32, plain, ![X57, X58, X59, X60, X61, X62]:k5_enumset1(X57,X57,X58,X59,X60,X61,X62)=k4_enumset1(X57,X58,X59,X60,X61,X62), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 20.81/21.01  fof(c_0_33, plain, ![X63, X64, X65, X66, X67, X68, X69]:k6_enumset1(X63,X63,X64,X65,X66,X67,X68,X69)=k5_enumset1(X63,X64,X65,X66,X67,X68,X69), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 20.81/21.01  fof(c_0_34, plain, ![X31, X32]:k2_xboole_0(X31,X32)=k5_xboole_0(X31,k4_xboole_0(X32,X31)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 20.81/21.01  fof(c_0_35, plain, ![X19, X20]:k4_xboole_0(X19,X20)=k5_xboole_0(X19,k3_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 20.81/21.01  fof(c_0_36, negated_conjecture, (((k1_tarski(esk4_0)=k2_xboole_0(esk5_0,esk6_0)&(esk5_0!=k1_tarski(esk4_0)|esk6_0!=k1_tarski(esk4_0)))&(esk5_0!=k1_xboole_0|esk6_0!=k1_tarski(esk4_0)))&(esk5_0!=k1_tarski(esk4_0)|esk6_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 20.81/21.01  fof(c_0_37, plain, ![X42]:k2_tarski(X42,X42)=k1_tarski(X42), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 20.81/21.01  cnf(c_0_38, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 20.81/21.01  cnf(c_0_39, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 20.81/21.01  fof(c_0_40, plain, ![X24]:k5_xboole_0(X24,k1_xboole_0)=X24, inference(variable_rename,[status(thm)],[t5_boole])).
% 20.81/21.01  cnf(c_0_41, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 20.81/21.01  cnf(c_0_42, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 20.81/21.01  cnf(c_0_43, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 20.81/21.01  cnf(c_0_44, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 20.81/21.01  cnf(c_0_45, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 20.81/21.01  cnf(c_0_46, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 20.81/21.01  cnf(c_0_47, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 20.81/21.01  cnf(c_0_48, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 20.81/21.01  cnf(c_0_49, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 20.81/21.01  cnf(c_0_50, negated_conjecture, (k1_tarski(esk4_0)=k2_xboole_0(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 20.81/21.01  cnf(c_0_51, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 20.81/21.01  cnf(c_0_52, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=k5_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 20.81/21.01  cnf(c_0_53, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_40])).
% 20.81/21.01  fof(c_0_54, plain, ![X70, X71]:((~r1_tarski(X70,k1_tarski(X71))|(X70=k1_xboole_0|X70=k1_tarski(X71)))&((X70!=k1_xboole_0|r1_tarski(X70,k1_tarski(X71)))&(X70!=k1_tarski(X71)|r1_tarski(X70,k1_tarski(X71))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 20.81/21.01  cnf(c_0_55, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])).
% 20.81/21.01  cnf(c_0_56, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_42]), c_0_49]), c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])).
% 20.81/21.01  cnf(c_0_57, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51]), c_0_28]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_47]), c_0_47])).
% 20.81/21.01  cnf(c_0_58, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_39]), c_0_53])).
% 20.81/21.01  cnf(c_0_59, plain, (r1_tarski(X1,k1_tarski(X2))|X1!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 20.81/21.01  cnf(c_0_60, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 20.81/21.01  cnf(c_0_61, plain, (r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 20.81/21.01  cnf(c_0_62, negated_conjecture, (k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,esk5_0)))=k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[c_0_57, c_0_56])).
% 20.81/21.01  cnf(c_0_63, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[c_0_52, c_0_58])).
% 20.81/21.01  cnf(c_0_64, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_38])).
% 20.81/21.01  fof(c_0_65, plain, ![X21, X22]:(~r1_tarski(X21,X22)|k2_xboole_0(X21,X22)=X22), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 20.81/21.01  cnf(c_0_66, plain, (r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))|X1!=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_51]), c_0_51]), c_0_28]), c_0_28]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_47]), c_0_47])).
% 20.81/21.01  cnf(c_0_67, plain, (X1=k1_xboole_0|X1=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|~r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_51]), c_0_51]), c_0_28]), c_0_28]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_47]), c_0_47])).
% 20.81/21.01  cnf(c_0_68, negated_conjecture, (r1_tarski(esk5_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 20.81/21.01  cnf(c_0_69, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_53])).
% 20.81/21.01  cnf(c_0_70, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 20.81/21.01  cnf(c_0_71, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))), inference(er,[status(thm)],[c_0_66])).
% 20.81/21.01  cnf(c_0_72, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=esk5_0|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 20.81/21.01  cnf(c_0_73, negated_conjecture, (k5_xboole_0(esk5_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))=k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,esk5_0))), inference(spm,[status(thm)],[c_0_63, c_0_62])).
% 20.81/21.01  cnf(c_0_74, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X1)))=k5_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_69, c_0_38])).
% 20.81/21.01  cnf(c_0_75, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])).
% 20.81/21.01  cnf(c_0_76, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 20.81/21.01  cnf(c_0_77, negated_conjecture, (k5_xboole_0(esk5_0,k5_xboole_0(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),X1))=k5_xboole_0(esk6_0,k5_xboole_0(k3_xboole_0(esk6_0,esk5_0),X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_73]), c_0_38])).
% 20.81/21.01  cnf(c_0_78, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))))=k5_xboole_0(X3,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_56]), c_0_38])).
% 20.81/21.01  cnf(c_0_79, negated_conjecture, (k3_xboole_0(esk5_0,esk5_0)=esk5_0|esk5_0=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_56]), c_0_63])).
% 20.81/21.01  cnf(c_0_80, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_63, c_0_69])).
% 20.81/21.01  fof(c_0_81, plain, ![X8, X9, X10, X11, X12, X13, X14, X15]:(((~r2_hidden(X11,X10)|(r2_hidden(X11,X8)|r2_hidden(X11,X9))|X10!=k2_xboole_0(X8,X9))&((~r2_hidden(X12,X8)|r2_hidden(X12,X10)|X10!=k2_xboole_0(X8,X9))&(~r2_hidden(X12,X9)|r2_hidden(X12,X10)|X10!=k2_xboole_0(X8,X9))))&(((~r2_hidden(esk1_3(X13,X14,X15),X13)|~r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k2_xboole_0(X13,X14))&(~r2_hidden(esk1_3(X13,X14,X15),X14)|~r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k2_xboole_0(X13,X14)))&(r2_hidden(esk1_3(X13,X14,X15),X15)|(r2_hidden(esk1_3(X13,X14,X15),X13)|r2_hidden(esk1_3(X13,X14,X15),X14))|X15=k2_xboole_0(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 20.81/21.01  cnf(c_0_82, negated_conjecture, (esk5_0!=k1_tarski(esk4_0)|esk6_0!=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 20.81/21.01  cnf(c_0_83, negated_conjecture, (k5_xboole_0(esk6_0,k5_xboole_0(k3_xboole_0(esk6_0,esk5_0),X1))=X1|esk5_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_72]), c_0_63])).
% 20.81/21.01  cnf(c_0_84, negated_conjecture, (k5_xboole_0(X1,k3_xboole_0(esk5_0,esk5_0))=k5_xboole_0(X1,esk5_0)|esk5_0=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_56]), c_0_63]), c_0_63])).
% 20.81/21.01  cnf(c_0_85, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X2,k5_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_38, c_0_80])).
% 20.81/21.01  cnf(c_0_86, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 20.81/21.01  cnf(c_0_87, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 20.81/21.01  fof(c_0_88, plain, ![X33, X34, X35, X36, X37, X38, X39, X40]:(((~r2_hidden(X36,X35)|(X36=X33|X36=X34)|X35!=k2_tarski(X33,X34))&((X37!=X33|r2_hidden(X37,X35)|X35!=k2_tarski(X33,X34))&(X37!=X34|r2_hidden(X37,X35)|X35!=k2_tarski(X33,X34))))&(((esk3_3(X38,X39,X40)!=X38|~r2_hidden(esk3_3(X38,X39,X40),X40)|X40=k2_tarski(X38,X39))&(esk3_3(X38,X39,X40)!=X39|~r2_hidden(esk3_3(X38,X39,X40),X40)|X40=k2_tarski(X38,X39)))&(r2_hidden(esk3_3(X38,X39,X40),X40)|(esk3_3(X38,X39,X40)=X38|esk3_3(X38,X39,X40)=X39)|X40=k2_tarski(X38,X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 20.81/21.01  cnf(c_0_89, negated_conjecture, (esk5_0!=k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)|esk6_0!=k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_51]), c_0_51]), c_0_28]), c_0_28]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_47]), c_0_47])).
% 20.81/21.01  cnf(c_0_90, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k3_xboole_0(esk5_0,esk5_0)|esk5_0=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_80]), c_0_85]), c_0_80]), c_0_62])).
% 20.81/21.01  cnf(c_0_91, plain, (X3=k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])).
% 20.81/21.01  cnf(c_0_92, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])).
% 20.81/21.01  fof(c_0_93, plain, ![X17]:(X17=k1_xboole_0|r2_hidden(esk2_1(X17),X17)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 20.81/21.01  cnf(c_0_94, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 20.81/21.01  cnf(c_0_95, negated_conjecture, (esk5_0=k1_xboole_0|k3_xboole_0(esk5_0,esk5_0)!=esk6_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_79])).
% 20.81/21.01  cnf(c_0_96, plain, (X1=k3_xboole_0(X2,X2)|r2_hidden(esk1_3(X2,X2,X1),X2)|r2_hidden(esk1_3(X2,X2,X1),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_91]), c_0_56]), c_0_63])).
% 20.81/21.01  cnf(c_0_97, plain, (r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_92])).
% 20.81/21.01  cnf(c_0_98, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 20.81/21.01  cnf(c_0_99, plain, (X1=X4|X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_28]), c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])).
% 20.81/21.01  cnf(c_0_100, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(esk1_3(esk5_0,esk5_0,esk6_0),esk6_0)|r2_hidden(esk1_3(esk5_0,esk5_0,esk6_0),esk5_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96])])).
% 20.81/21.01  cnf(c_0_101, negated_conjecture, (k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,esk5_0))=k1_xboole_0|esk5_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_72]), c_0_39])).
% 20.81/21.01  cnf(c_0_102, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 20.81/21.01  cnf(c_0_103, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 20.81/21.01  cnf(c_0_104, plain, (X1=X2|X1=X3|~r2_hidden(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_99])).
% 20.81/21.01  cnf(c_0_105, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(esk1_3(esk5_0,esk5_0,esk6_0),k5_xboole_0(X1,k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,X1))))|r2_hidden(esk1_3(esk5_0,esk5_0,esk6_0),esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_100]), c_0_56])).
% 20.81/21.01  cnf(c_0_106, negated_conjecture, (k3_xboole_0(esk6_0,esk5_0)=esk6_0|esk5_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_101]), c_0_53])).
% 20.81/21.01  cnf(c_0_107, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_28]), c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])).
% 20.81/21.01  cnf(c_0_108, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))))), inference(spm,[status(thm)],[c_0_103, c_0_56])).
% 20.81/21.01  cnf(c_0_109, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 20.81/21.01  cnf(c_0_110, negated_conjecture, (esk5_0=k1_xboole_0|X1=esk4_0|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_104, c_0_72])).
% 20.81/21.01  cnf(c_0_111, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(esk1_3(esk5_0,esk5_0,esk6_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_39]), c_0_53])])).
% 20.81/21.01  cnf(c_0_112, plain, (r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_107])])).
% 20.81/21.01  cnf(c_0_113, negated_conjecture, (esk5_0=k1_xboole_0|esk6_0=k1_xboole_0|r2_hidden(esk2_1(esk6_0),esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_106]), c_0_39]), c_0_53])).
% 20.81/21.01  cnf(c_0_114, plain, (X3=k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])).
% 20.81/21.01  cnf(c_0_115, negated_conjecture, (esk1_3(esk5_0,esk5_0,esk6_0)=esk4_0|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_110, c_0_111])).
% 20.81/21.01  cnf(c_0_116, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_112, c_0_72])).
% 20.81/21.01  cnf(c_0_117, negated_conjecture, (esk5_0!=k1_tarski(esk4_0)|esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_36])).
% 20.81/21.01  cnf(c_0_118, negated_conjecture, (esk2_1(esk6_0)=esk4_0|esk6_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_110, c_0_113])).
% 20.81/21.01  cnf(c_0_119, negated_conjecture, (esk5_0=k1_xboole_0|~r2_hidden(esk4_0,esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_56]), c_0_63]), c_0_116]), c_0_95])).
% 20.81/21.01  cnf(c_0_120, negated_conjecture, (esk5_0!=k1_xboole_0|esk6_0!=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 20.81/21.01  cnf(c_0_121, negated_conjecture, (esk6_0!=k1_xboole_0|esk5_0!=k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117, c_0_51]), c_0_28]), c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])).
% 20.81/21.01  cnf(c_0_122, negated_conjecture, (esk5_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_118]), c_0_119])).
% 20.81/21.01  cnf(c_0_123, negated_conjecture, (k5_xboole_0(esk6_0,k5_xboole_0(k3_xboole_0(esk6_0,esk5_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_73]), c_0_80]), c_0_38])).
% 20.81/21.01  fof(c_0_124, plain, ![X23]:k3_xboole_0(X23,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 20.81/21.01  cnf(c_0_125, negated_conjecture, (esk5_0!=k1_xboole_0|esk6_0!=k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_120, c_0_51]), c_0_28]), c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])).
% 20.81/21.01  cnf(c_0_126, negated_conjecture, (esk5_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_122]), c_0_72])).
% 20.81/21.01  cnf(c_0_127, negated_conjecture, (k5_xboole_0(k3_xboole_0(esk6_0,esk5_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))=k5_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_123]), c_0_80])).
% 20.81/21.01  cnf(c_0_128, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_124])).
% 20.81/21.01  cnf(c_0_129, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)!=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_125, c_0_126])])).
% 20.81/21.01  cnf(c_0_130, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_127, c_0_126]), c_0_128]), c_0_58]), c_0_126]), c_0_58]), c_0_129]), ['proof']).
% 20.81/21.01  # SZS output end CNFRefutation
% 20.81/21.01  # Proof object total steps             : 131
% 20.81/21.01  # Proof object clause steps            : 88
% 20.81/21.01  # Proof object formula steps           : 43
% 20.81/21.01  # Proof object conjectures             : 39
% 20.81/21.01  # Proof object clause conjectures      : 36
% 20.81/21.01  # Proof object formula conjectures     : 3
% 20.81/21.01  # Proof object initial clauses used    : 28
% 20.81/21.01  # Proof object initial formulas used   : 21
% 20.81/21.01  # Proof object generating inferences   : 37
% 20.81/21.01  # Proof object simplifying inferences  : 169
% 20.81/21.01  # Training examples: 0 positive, 0 negative
% 20.81/21.01  # Parsed axioms                        : 22
% 20.81/21.01  # Removed by relevancy pruning/SinE    : 0
% 20.81/21.01  # Initial clauses                      : 39
% 20.81/21.01  # Removed in clause preprocessing      : 9
% 20.81/21.01  # Initial clauses in saturation        : 30
% 20.81/21.01  # Processed clauses                    : 8746
% 20.81/21.01  # ...of these trivial                  : 82
% 20.81/21.01  # ...subsumed                          : 7367
% 20.81/21.01  # ...remaining for further processing  : 1296
% 20.81/21.01  # Other redundant clauses eliminated   : 1134
% 20.81/21.01  # Clauses deleted for lack of memory   : 0
% 20.81/21.01  # Backward-subsumed                    : 57
% 20.81/21.01  # Backward-rewritten                   : 892
% 20.81/21.01  # Generated clauses                    : 421620
% 20.81/21.01  # ...of the previous two non-trivial   : 418235
% 20.81/21.01  # Contextual simplify-reflections      : 9
% 20.81/21.01  # Paramodulations                      : 417757
% 20.81/21.01  # Factorizations                       : 2730
% 20.81/21.01  # Equation resolutions                 : 1134
% 20.81/21.01  # Propositional unsat checks           : 0
% 20.81/21.01  #    Propositional check models        : 0
% 20.81/21.01  #    Propositional check unsatisfiable : 0
% 20.81/21.01  #    Propositional clauses             : 0
% 20.81/21.01  #    Propositional clauses after purity: 0
% 20.81/21.01  #    Propositional unsat core size     : 0
% 20.81/21.01  #    Propositional preprocessing time  : 0.000
% 20.81/21.01  #    Propositional encoding time       : 0.000
% 20.81/21.01  #    Propositional solver time         : 0.000
% 20.81/21.01  #    Success case prop preproc time    : 0.000
% 20.81/21.01  #    Success case prop encoding time   : 0.000
% 20.81/21.01  #    Success case prop solver time     : 0.000
% 20.81/21.01  # Current number of processed clauses  : 308
% 20.81/21.01  #    Positive orientable unit clauses  : 45
% 20.81/21.01  #    Positive unorientable unit clauses: 9
% 20.81/21.01  #    Negative unit clauses             : 1
% 20.81/21.01  #    Non-unit-clauses                  : 253
% 20.81/21.01  # Current number of unprocessed clauses: 409086
% 20.81/21.01  # ...number of literals in the above   : 4338436
% 20.81/21.01  # Current number of archived formulas  : 0
% 20.81/21.01  # Current number of archived clauses   : 989
% 20.81/21.01  # Clause-clause subsumption calls (NU) : 428601
% 20.81/21.01  # Rec. Clause-clause subsumption calls : 120501
% 20.81/21.01  # Non-unit clause-clause subsumptions  : 7370
% 20.81/21.01  # Unit Clause-clause subsumption calls : 778
% 20.81/21.01  # Rewrite failures with RHS unbound    : 0
% 20.81/21.01  # BW rewrite match attempts            : 1011
% 20.81/21.01  # BW rewrite match successes           : 350
% 20.81/21.01  # Condensation attempts                : 0
% 20.81/21.01  # Condensation successes               : 0
% 20.81/21.01  # Termbank termtop insertions          : 21214654
% 20.85/21.03  
% 20.85/21.03  # -------------------------------------------------
% 20.85/21.03  # User time                : 20.418 s
% 20.85/21.03  # System time              : 0.279 s
% 20.85/21.03  # Total time               : 20.697 s
% 20.85/21.03  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
