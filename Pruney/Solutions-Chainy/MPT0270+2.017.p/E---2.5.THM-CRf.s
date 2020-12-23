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
% DateTime   : Thu Dec  3 10:42:38 EST 2020

% Result     : Theorem 36.54s
% Output     : CNFRefutation 36.54s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 430 expanded)
%              Number of clauses        :   45 ( 165 expanded)
%              Number of leaves         :   20 ( 131 expanded)
%              Depth                    :    9
%              Number of atoms          :  188 ( 646 expanded)
%              Number of equality atoms :  102 ( 494 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t67_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
    <=> ~ r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

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

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t60_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,X2)
     => ( ( r2_hidden(X3,X2)
          & X1 != X3 )
        | k3_xboole_0(k2_tarski(X1,X3),X2) = k1_tarski(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(l97_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t112_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

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

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
      <=> ~ r2_hidden(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t67_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X45,X46,X47,X48,X49,X50,X51,X52,X53,X54] :
      ( ( ~ r2_hidden(X49,X48)
        | X49 = X45
        | X49 = X46
        | X49 = X47
        | X48 != k1_enumset1(X45,X46,X47) )
      & ( X50 != X45
        | r2_hidden(X50,X48)
        | X48 != k1_enumset1(X45,X46,X47) )
      & ( X50 != X46
        | r2_hidden(X50,X48)
        | X48 != k1_enumset1(X45,X46,X47) )
      & ( X50 != X47
        | r2_hidden(X50,X48)
        | X48 != k1_enumset1(X45,X46,X47) )
      & ( esk4_4(X51,X52,X53,X54) != X51
        | ~ r2_hidden(esk4_4(X51,X52,X53,X54),X54)
        | X54 = k1_enumset1(X51,X52,X53) )
      & ( esk4_4(X51,X52,X53,X54) != X52
        | ~ r2_hidden(esk4_4(X51,X52,X53,X54),X54)
        | X54 = k1_enumset1(X51,X52,X53) )
      & ( esk4_4(X51,X52,X53,X54) != X53
        | ~ r2_hidden(esk4_4(X51,X52,X53,X54),X54)
        | X54 = k1_enumset1(X51,X52,X53) )
      & ( r2_hidden(esk4_4(X51,X52,X53,X54),X54)
        | esk4_4(X51,X52,X53,X54) = X51
        | esk4_4(X51,X52,X53,X54) = X52
        | esk4_4(X51,X52,X53,X54) = X53
        | X54 = k1_enumset1(X51,X52,X53) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_22,plain,(
    ! [X63,X64,X65] : k2_enumset1(X63,X63,X64,X65) = k1_enumset1(X63,X64,X65) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_23,plain,(
    ! [X66,X67,X68,X69] : k3_enumset1(X66,X66,X67,X68,X69) = k2_enumset1(X66,X67,X68,X69) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_24,plain,(
    ! [X70,X71,X72,X73,X74] : k4_enumset1(X70,X70,X71,X72,X73,X74) = k3_enumset1(X70,X71,X72,X73,X74) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_25,plain,(
    ! [X75,X76,X77,X78,X79,X80] : k5_enumset1(X75,X75,X76,X77,X78,X79,X80) = k4_enumset1(X75,X76,X77,X78,X79,X80) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_26,plain,(
    ! [X81,X82,X83,X84,X85,X86,X87] : k6_enumset1(X81,X81,X82,X83,X84,X85,X86,X87) = k5_enumset1(X81,X82,X83,X84,X85,X86,X87) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_27,negated_conjecture,
    ( ( k4_xboole_0(k1_tarski(esk5_0),esk6_0) != k1_tarski(esk5_0)
      | r2_hidden(esk5_0,esk6_0) )
    & ( k4_xboole_0(k1_tarski(esk5_0),esk6_0) = k1_tarski(esk5_0)
      | ~ r2_hidden(esk5_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).

fof(c_0_28,plain,(
    ! [X60] : k2_tarski(X60,X60) = k1_tarski(X60) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_29,plain,(
    ! [X61,X62] : k1_enumset1(X61,X61,X62) = k2_tarski(X61,X62) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_30,plain,(
    ! [X37,X38] : k4_xboole_0(X37,X38) = k5_xboole_0(X37,k3_xboole_0(X37,X38)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_31,plain,(
    ! [X88,X89,X90] :
      ( ( r2_hidden(X90,X89)
        | k3_xboole_0(k2_tarski(X88,X90),X89) = k1_tarski(X88)
        | ~ r2_hidden(X88,X89) )
      & ( X88 != X90
        | k3_xboole_0(k2_tarski(X88,X90),X89) = k1_tarski(X88)
        | ~ r2_hidden(X88,X89) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_zfmisc_1])])])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_38,plain,(
    ! [X21,X22] :
      ( ( ~ r1_xboole_0(X21,X22)
        | k3_xboole_0(X21,X22) = k1_xboole_0 )
      & ( k3_xboole_0(X21,X22) != k1_xboole_0
        | r1_xboole_0(X21,X22) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_39,plain,(
    ! [X35,X36] : r1_xboole_0(k3_xboole_0(X35,X36),k5_xboole_0(X35,X36)) ),
    inference(variable_rename,[status(thm)],[l97_xboole_1])).

fof(c_0_40,plain,(
    ! [X42,X43,X44] : k3_xboole_0(k3_xboole_0(X42,X43),X44) = k3_xboole_0(X42,k3_xboole_0(X43,X44)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0)
    | k4_xboole_0(k1_tarski(esk5_0),esk6_0) != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_45,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_46,plain,(
    ! [X39,X40,X41] : k5_xboole_0(k3_xboole_0(X39,X40),k3_xboole_0(X41,X40)) = k3_xboole_0(k5_xboole_0(X39,X41),X40) ),
    inference(variable_rename,[status(thm)],[t112_xboole_1])).

fof(c_0_47,plain,(
    ! [X23] : k3_xboole_0(X23,X23) = X23 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_48,plain,(
    ! [X10,X11] : k5_xboole_0(X10,X11) = k5_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_49,plain,
    ( k3_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    | X1 != X2
    | ~ r2_hidden(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_50,plain,(
    ! [X24,X25,X26] :
      ( ( ~ r2_hidden(X24,X25)
        | ~ r2_hidden(X24,X26)
        | ~ r2_hidden(X24,k5_xboole_0(X25,X26)) )
      & ( r2_hidden(X24,X25)
        | r2_hidden(X24,X26)
        | ~ r2_hidden(X24,k5_xboole_0(X25,X26)) )
      & ( ~ r2_hidden(X24,X25)
        | r2_hidden(X24,X26)
        | r2_hidden(X24,k5_xboole_0(X25,X26)) )
      & ( ~ r2_hidden(X24,X26)
        | r2_hidden(X24,X25)
        | r2_hidden(X24,k5_xboole_0(X25,X26)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_52,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_53,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_54,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0)
    | k5_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)) != k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_33]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,plain,
    ( k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | X1 != X2
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_42]),c_0_43]),c_0_43]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X3,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_51])])).

cnf(c_0_63,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk5_0),esk6_0) = k1_tarski(esk5_0)
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_64,plain,(
    ! [X27,X28,X30,X31,X32] :
      ( ( r2_hidden(esk2_2(X27,X28),X27)
        | r1_xboole_0(X27,X28) )
      & ( r2_hidden(esk2_2(X27,X28),X28)
        | r1_xboole_0(X27,X28) )
      & ( ~ r2_hidden(X32,X30)
        | ~ r2_hidden(X32,X31)
        | ~ r1_xboole_0(X30,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_65,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_66,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0)
    | k5_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(esk6_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) != k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_68,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,k5_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_56])).

cnf(c_0_69,plain,
    ( k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X1)))
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_71,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)) = k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_33]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_72,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_73,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0)
    | k3_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_xboole_0(esk6_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) != k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_75,plain,
    ( k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X1))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(esk6_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) = k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_71,c_0_56])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_78,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k5_xboole_0(X3,X2)))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_xboole_0(esk6_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) = k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_76,c_0_68])).

cnf(c_0_81,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X2,X2,X2,X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_82,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k3_xboole_0(X1,k5_xboole_0(esk6_0,X1))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_xboole_0(esk6_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) = k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_79])])).

cnf(c_0_84,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_81])])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84])]),
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
% 0.13/0.34  % DateTime   : Tue Dec  1 14:35:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 36.54/36.78  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 36.54/36.78  # and selection function GSelectMinInfpos.
% 36.54/36.78  #
% 36.54/36.78  # Preprocessing time       : 0.029 s
% 36.54/36.78  # Presaturation interreduction done
% 36.54/36.78  
% 36.54/36.78  # Proof found!
% 36.54/36.78  # SZS status Theorem
% 36.54/36.78  # SZS output start CNFRefutation
% 36.54/36.78  fof(t67_zfmisc_1, conjecture, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)<=>~(r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 36.54/36.78  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 36.54/36.78  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 36.54/36.78  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 36.54/36.78  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 36.54/36.78  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 36.54/36.78  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 36.54/36.78  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 36.54/36.78  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 36.54/36.78  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 36.54/36.78  fof(t60_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,X2)=>((r2_hidden(X3,X2)&X1!=X3)|k3_xboole_0(k2_tarski(X1,X3),X2)=k1_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_zfmisc_1)).
% 36.54/36.78  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 36.54/36.78  fof(l97_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 36.54/36.78  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 36.54/36.78  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 36.54/36.78  fof(t112_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 36.54/36.78  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 36.54/36.78  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 36.54/36.78  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 36.54/36.78  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 36.54/36.78  fof(c_0_20, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)<=>~(r2_hidden(X1,X2)))), inference(assume_negation,[status(cth)],[t67_zfmisc_1])).
% 36.54/36.78  fof(c_0_21, plain, ![X45, X46, X47, X48, X49, X50, X51, X52, X53, X54]:(((~r2_hidden(X49,X48)|(X49=X45|X49=X46|X49=X47)|X48!=k1_enumset1(X45,X46,X47))&(((X50!=X45|r2_hidden(X50,X48)|X48!=k1_enumset1(X45,X46,X47))&(X50!=X46|r2_hidden(X50,X48)|X48!=k1_enumset1(X45,X46,X47)))&(X50!=X47|r2_hidden(X50,X48)|X48!=k1_enumset1(X45,X46,X47))))&((((esk4_4(X51,X52,X53,X54)!=X51|~r2_hidden(esk4_4(X51,X52,X53,X54),X54)|X54=k1_enumset1(X51,X52,X53))&(esk4_4(X51,X52,X53,X54)!=X52|~r2_hidden(esk4_4(X51,X52,X53,X54),X54)|X54=k1_enumset1(X51,X52,X53)))&(esk4_4(X51,X52,X53,X54)!=X53|~r2_hidden(esk4_4(X51,X52,X53,X54),X54)|X54=k1_enumset1(X51,X52,X53)))&(r2_hidden(esk4_4(X51,X52,X53,X54),X54)|(esk4_4(X51,X52,X53,X54)=X51|esk4_4(X51,X52,X53,X54)=X52|esk4_4(X51,X52,X53,X54)=X53)|X54=k1_enumset1(X51,X52,X53)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 36.54/36.78  fof(c_0_22, plain, ![X63, X64, X65]:k2_enumset1(X63,X63,X64,X65)=k1_enumset1(X63,X64,X65), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 36.54/36.78  fof(c_0_23, plain, ![X66, X67, X68, X69]:k3_enumset1(X66,X66,X67,X68,X69)=k2_enumset1(X66,X67,X68,X69), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 36.54/36.78  fof(c_0_24, plain, ![X70, X71, X72, X73, X74]:k4_enumset1(X70,X70,X71,X72,X73,X74)=k3_enumset1(X70,X71,X72,X73,X74), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 36.54/36.78  fof(c_0_25, plain, ![X75, X76, X77, X78, X79, X80]:k5_enumset1(X75,X75,X76,X77,X78,X79,X80)=k4_enumset1(X75,X76,X77,X78,X79,X80), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 36.54/36.78  fof(c_0_26, plain, ![X81, X82, X83, X84, X85, X86, X87]:k6_enumset1(X81,X81,X82,X83,X84,X85,X86,X87)=k5_enumset1(X81,X82,X83,X84,X85,X86,X87), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 36.54/36.78  fof(c_0_27, negated_conjecture, ((k4_xboole_0(k1_tarski(esk5_0),esk6_0)!=k1_tarski(esk5_0)|r2_hidden(esk5_0,esk6_0))&(k4_xboole_0(k1_tarski(esk5_0),esk6_0)=k1_tarski(esk5_0)|~r2_hidden(esk5_0,esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).
% 36.54/36.78  fof(c_0_28, plain, ![X60]:k2_tarski(X60,X60)=k1_tarski(X60), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 36.54/36.78  fof(c_0_29, plain, ![X61, X62]:k1_enumset1(X61,X61,X62)=k2_tarski(X61,X62), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 36.54/36.78  fof(c_0_30, plain, ![X37, X38]:k4_xboole_0(X37,X38)=k5_xboole_0(X37,k3_xboole_0(X37,X38)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 36.54/36.78  fof(c_0_31, plain, ![X88, X89, X90]:((r2_hidden(X90,X89)|k3_xboole_0(k2_tarski(X88,X90),X89)=k1_tarski(X88)|~r2_hidden(X88,X89))&(X88!=X90|k3_xboole_0(k2_tarski(X88,X90),X89)=k1_tarski(X88)|~r2_hidden(X88,X89))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_zfmisc_1])])])).
% 36.54/36.78  cnf(c_0_32, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 36.54/36.78  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 36.54/36.78  cnf(c_0_34, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 36.54/36.78  cnf(c_0_35, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 36.54/36.78  cnf(c_0_36, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 36.54/36.78  cnf(c_0_37, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 36.54/36.78  fof(c_0_38, plain, ![X21, X22]:((~r1_xboole_0(X21,X22)|k3_xboole_0(X21,X22)=k1_xboole_0)&(k3_xboole_0(X21,X22)!=k1_xboole_0|r1_xboole_0(X21,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 36.54/36.78  fof(c_0_39, plain, ![X35, X36]:r1_xboole_0(k3_xboole_0(X35,X36),k5_xboole_0(X35,X36)), inference(variable_rename,[status(thm)],[l97_xboole_1])).
% 36.54/36.78  fof(c_0_40, plain, ![X42, X43, X44]:k3_xboole_0(k3_xboole_0(X42,X43),X44)=k3_xboole_0(X42,k3_xboole_0(X43,X44)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 36.54/36.78  cnf(c_0_41, negated_conjecture, (r2_hidden(esk5_0,esk6_0)|k4_xboole_0(k1_tarski(esk5_0),esk6_0)!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 36.54/36.78  cnf(c_0_42, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 36.54/36.78  cnf(c_0_43, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 36.54/36.78  cnf(c_0_44, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 36.54/36.78  fof(c_0_45, plain, ![X8, X9]:k3_xboole_0(X8,X9)=k3_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 36.54/36.78  fof(c_0_46, plain, ![X39, X40, X41]:k5_xboole_0(k3_xboole_0(X39,X40),k3_xboole_0(X41,X40))=k3_xboole_0(k5_xboole_0(X39,X41),X40), inference(variable_rename,[status(thm)],[t112_xboole_1])).
% 36.54/36.78  fof(c_0_47, plain, ![X23]:k3_xboole_0(X23,X23)=X23, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 36.54/36.78  fof(c_0_48, plain, ![X10, X11]:k5_xboole_0(X10,X11)=k5_xboole_0(X11,X10), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 36.54/36.78  cnf(c_0_49, plain, (k3_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)|X1!=X2|~r2_hidden(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 36.54/36.78  fof(c_0_50, plain, ![X24, X25, X26]:(((~r2_hidden(X24,X25)|~r2_hidden(X24,X26)|~r2_hidden(X24,k5_xboole_0(X25,X26)))&(r2_hidden(X24,X25)|r2_hidden(X24,X26)|~r2_hidden(X24,k5_xboole_0(X25,X26))))&((~r2_hidden(X24,X25)|r2_hidden(X24,X26)|r2_hidden(X24,k5_xboole_0(X25,X26)))&(~r2_hidden(X24,X26)|r2_hidden(X24,X25)|r2_hidden(X24,k5_xboole_0(X25,X26))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 36.54/36.78  cnf(c_0_51, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37])).
% 36.54/36.78  cnf(c_0_52, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 36.54/36.78  cnf(c_0_53, plain, (r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 36.54/36.78  cnf(c_0_54, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 36.54/36.78  cnf(c_0_55, negated_conjecture, (r2_hidden(esk5_0,esk6_0)|k5_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0))!=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_33]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37])).
% 36.54/36.78  cnf(c_0_56, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 36.54/36.78  cnf(c_0_57, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 36.54/36.78  cnf(c_0_58, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_47])).
% 36.54/36.78  cnf(c_0_59, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 36.54/36.78  cnf(c_0_60, plain, (k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3)=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)|X1!=X2|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_42]), c_0_43]), c_0_43]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 36.54/36.78  cnf(c_0_61, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X3,X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 36.54/36.78  cnf(c_0_62, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_51])])).
% 36.54/36.78  cnf(c_0_63, negated_conjecture, (k4_xboole_0(k1_tarski(esk5_0),esk6_0)=k1_tarski(esk5_0)|~r2_hidden(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 36.54/36.78  fof(c_0_64, plain, ![X27, X28, X30, X31, X32]:(((r2_hidden(esk2_2(X27,X28),X27)|r1_xboole_0(X27,X28))&(r2_hidden(esk2_2(X27,X28),X28)|r1_xboole_0(X27,X28)))&(~r2_hidden(X32,X30)|~r2_hidden(X32,X31)|~r1_xboole_0(X30,X31))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 36.54/36.78  cnf(c_0_65, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_38])).
% 36.54/36.78  cnf(c_0_66, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X1,X2)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])).
% 36.54/36.78  cnf(c_0_67, negated_conjecture, (r2_hidden(esk5_0,esk6_0)|k5_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(esk6_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))!=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[c_0_55, c_0_56])).
% 36.54/36.78  cnf(c_0_68, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X1,k5_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_56])).
% 36.54/36.78  cnf(c_0_69, plain, (k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_60])).
% 36.54/36.78  cnf(c_0_70, plain, (r2_hidden(X1,k5_xboole_0(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X1)))|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 36.54/36.78  cnf(c_0_71, negated_conjecture, (k5_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0))=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)|~r2_hidden(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_33]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37])).
% 36.54/36.78  cnf(c_0_72, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 36.54/36.78  cnf(c_0_73, plain, (r1_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 36.54/36.78  cnf(c_0_74, negated_conjecture, (r2_hidden(esk5_0,esk6_0)|k3_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_xboole_0(esk6_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))!=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[c_0_67, c_0_68])).
% 36.54/36.78  cnf(c_0_75, plain, (k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X1)))=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 36.54/36.78  cnf(c_0_76, negated_conjecture, (k5_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(esk6_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)|~r2_hidden(esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_71, c_0_56])).
% 36.54/36.78  cnf(c_0_77, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 36.54/36.78  cnf(c_0_78, plain, (~r2_hidden(X1,k3_xboole_0(X2,k5_xboole_0(X3,X2)))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 36.54/36.78  cnf(c_0_79, negated_conjecture, (r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 36.54/36.78  cnf(c_0_80, negated_conjecture, (k3_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_xboole_0(esk6_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)|~r2_hidden(esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_76, c_0_68])).
% 36.54/36.78  cnf(c_0_81, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X2,X2,X2,X2,X2,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37])).
% 36.54/36.78  cnf(c_0_82, negated_conjecture, (~r2_hidden(esk5_0,k3_xboole_0(X1,k5_xboole_0(esk6_0,X1)))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 36.54/36.78  cnf(c_0_83, negated_conjecture, (k3_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_xboole_0(esk6_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_79])])).
% 36.54/36.78  cnf(c_0_84, plain, (r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_81])])).
% 36.54/36.78  cnf(c_0_85, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84])]), ['proof']).
% 36.54/36.78  # SZS output end CNFRefutation
% 36.54/36.78  # Proof object total steps             : 86
% 36.54/36.78  # Proof object clause steps            : 45
% 36.54/36.78  # Proof object formula steps           : 41
% 36.54/36.78  # Proof object conjectures             : 15
% 36.54/36.78  # Proof object clause conjectures      : 12
% 36.54/36.78  # Proof object formula conjectures     : 3
% 36.54/36.78  # Proof object initial clauses used    : 23
% 36.54/36.78  # Proof object initial formulas used   : 20
% 36.54/36.78  # Proof object generating inferences   : 9
% 36.54/36.78  # Proof object simplifying inferences  : 79
% 36.54/36.78  # Training examples: 0 positive, 0 negative
% 36.54/36.78  # Parsed axioms                        : 23
% 36.54/36.78  # Removed by relevancy pruning/SinE    : 0
% 36.54/36.78  # Initial clauses                      : 43
% 36.54/36.78  # Removed in clause preprocessing      : 8
% 36.54/36.78  # Initial clauses in saturation        : 35
% 36.54/36.78  # Processed clauses                    : 40706
% 36.54/36.78  # ...of these trivial                  : 1082
% 36.54/36.78  # ...subsumed                          : 36158
% 36.54/36.78  # ...remaining for further processing  : 3466
% 36.54/36.78  # Other redundant clauses eliminated   : 696
% 36.54/36.78  # Clauses deleted for lack of memory   : 158772
% 36.54/36.78  # Backward-subsumed                    : 110
% 36.54/36.78  # Backward-rewritten                   : 280
% 36.54/36.78  # Generated clauses                    : 2134895
% 36.54/36.78  # ...of the previous two non-trivial   : 2006971
% 36.54/36.78  # Contextual simplify-reflections      : 0
% 36.54/36.78  # Paramodulations                      : 2133473
% 36.54/36.78  # Factorizations                       : 728
% 36.54/36.78  # Equation resolutions                 : 697
% 36.54/36.78  # Propositional unsat checks           : 0
% 36.54/36.78  #    Propositional check models        : 0
% 36.54/36.78  #    Propositional check unsatisfiable : 0
% 36.54/36.78  #    Propositional clauses             : 0
% 36.54/36.78  #    Propositional clauses after purity: 0
% 36.54/36.78  #    Propositional unsat core size     : 0
% 36.54/36.78  #    Propositional preprocessing time  : 0.000
% 36.54/36.78  #    Propositional encoding time       : 0.000
% 36.54/36.78  #    Propositional solver time         : 0.000
% 36.54/36.78  #    Success case prop preproc time    : 0.000
% 36.54/36.78  #    Success case prop encoding time   : 0.000
% 36.54/36.78  #    Success case prop solver time     : 0.000
% 36.54/36.78  # Current number of processed clauses  : 3033
% 36.54/36.78  #    Positive orientable unit clauses  : 386
% 36.54/36.78  #    Positive unorientable unit clauses: 16
% 36.54/36.78  #    Negative unit clauses             : 51
% 36.54/36.78  #    Non-unit-clauses                  : 2580
% 36.54/36.78  # Current number of unprocessed clauses: 1025127
% 36.54/36.78  # ...number of literals in the above   : 3347703
% 36.54/36.78  # Current number of archived formulas  : 0
% 36.54/36.78  # Current number of archived clauses   : 433
% 36.54/36.78  # Clause-clause subsumption calls (NU) : 916226
% 36.54/36.78  # Rec. Clause-clause subsumption calls : 801652
% 36.54/36.78  # Non-unit clause-clause subsumptions  : 11362
% 36.54/36.78  # Unit Clause-clause subsumption calls : 21700
% 36.54/36.78  # Rewrite failures with RHS unbound    : 0
% 36.54/36.78  # BW rewrite match attempts            : 7115
% 36.54/36.78  # BW rewrite match successes           : 647
% 36.54/36.78  # Condensation attempts                : 0
% 36.54/36.78  # Condensation successes               : 0
% 36.54/36.78  # Termbank termtop insertions          : 61066297
% 36.62/36.86  
% 36.62/36.86  # -------------------------------------------------
% 36.62/36.86  # User time                : 35.485 s
% 36.62/36.86  # System time              : 1.018 s
% 36.62/36.86  # Total time               : 36.502 s
% 36.62/36.86  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
