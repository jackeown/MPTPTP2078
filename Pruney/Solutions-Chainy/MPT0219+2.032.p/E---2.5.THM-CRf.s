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
% DateTime   : Thu Dec  3 10:37:22 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 316 expanded)
%              Number of clauses        :   38 ( 132 expanded)
%              Number of leaves         :   18 (  91 expanded)
%              Depth                    :   11
%              Number of atoms          :  185 ( 429 expanded)
%              Number of equality atoms :  151 ( 395 expanded)
%              Maximal formula depth    :   52 (   4 average)
%              Maximal clause size      :   76 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(t13_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t132_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_enumset1)).

fof(d7_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( X10 = k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)
    <=> ! [X11] :
          ( r2_hidden(X11,X10)
        <=> ~ ( X11 != X1
              & X11 != X2
              & X11 != X3
              & X11 != X4
              & X11 != X5
              & X11 != X6
              & X11 != X7
              & X11 != X8
              & X11 != X9 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_enumset1)).

fof(c_0_18,plain,(
    ! [X26,X27] : k2_xboole_0(X26,X27) = k5_xboole_0(X26,k4_xboole_0(X27,X26)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_19,plain,(
    ! [X16,X17] : k4_xboole_0(X16,X17) = k5_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_20,plain,(
    ! [X20,X21] : k4_xboole_0(X20,k2_xboole_0(X20,X21)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X18,X19] : k3_xboole_0(X18,k2_xboole_0(X18,X19)) = X18 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t13_zfmisc_1])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X22] : k5_xboole_0(X22,k1_xboole_0) = X22 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_29,plain,(
    ! [X14,X15] : k5_xboole_0(X14,X15) = k5_xboole_0(X15,X14) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_30,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0)) = k1_tarski(esk3_0)
    & esk3_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

fof(c_0_31,plain,(
    ! [X67] : k2_tarski(X67,X67) = k1_tarski(X67) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_32,plain,(
    ! [X68,X69] : k1_enumset1(X68,X68,X69) = k2_tarski(X68,X69) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_33,plain,(
    ! [X70,X71,X72] : k2_enumset1(X70,X70,X71,X72) = k1_enumset1(X70,X71,X72) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_34,plain,(
    ! [X73,X74,X75,X76] : k3_enumset1(X73,X73,X74,X75,X76) = k2_enumset1(X73,X74,X75,X76) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_35,plain,(
    ! [X77,X78,X79,X80,X81] : k4_enumset1(X77,X77,X78,X79,X80,X81) = k3_enumset1(X77,X78,X79,X80,X81) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_36,plain,(
    ! [X82,X83,X84,X85,X86,X87] : k5_enumset1(X82,X82,X83,X84,X85,X86,X87) = k4_enumset1(X82,X83,X84,X85,X86,X87) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_37,plain,(
    ! [X23,X24,X25] : k5_xboole_0(k5_xboole_0(X23,X24),X25) = k5_xboole_0(X23,k5_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_38,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_22]),c_0_26])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = X1 ),
    inference(rw,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0)) = k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_49,plain,(
    ! [X12,X13] : k3_xboole_0(X12,X13) = k3_xboole_0(X13,X12) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_50,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_52,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_53,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) = k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_26]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48])).

cnf(c_0_54,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_55,plain,(
    ! [X28,X29,X30,X31,X32,X33] :
      ( ( ~ r2_hidden(X30,X29)
        | X30 = X28
        | X29 != k1_tarski(X28) )
      & ( X31 != X28
        | r2_hidden(X31,X29)
        | X29 != k1_tarski(X28) )
      & ( ~ r2_hidden(esk1_2(X32,X33),X33)
        | esk1_2(X32,X33) != X32
        | X33 = k1_tarski(X32) )
      & ( r2_hidden(esk1_2(X32,X33),X33)
        | esk1_2(X32,X33) = X32
        | X33 = k1_tarski(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_56,plain,(
    ! [X58,X59,X60,X61,X62,X63,X64,X65,X66] : k7_enumset1(X58,X59,X60,X61,X62,X63,X64,X65,X66) = k2_xboole_0(k4_enumset1(X58,X59,X60,X61,X62,X63),k1_enumset1(X64,X65,X66)) ),
    inference(variable_rename,[status(thm)],[t132_enumset1])).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))) = k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_60,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_51])).

fof(c_0_62,plain,(
    ! [X35,X36,X37,X38,X39,X40,X41,X42,X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53,X54,X55,X56] :
      ( ( ~ r2_hidden(X45,X44)
        | X45 = X35
        | X45 = X36
        | X45 = X37
        | X45 = X38
        | X45 = X39
        | X45 = X40
        | X45 = X41
        | X45 = X42
        | X45 = X43
        | X44 != k7_enumset1(X35,X36,X37,X38,X39,X40,X41,X42,X43) )
      & ( X46 != X35
        | r2_hidden(X46,X44)
        | X44 != k7_enumset1(X35,X36,X37,X38,X39,X40,X41,X42,X43) )
      & ( X46 != X36
        | r2_hidden(X46,X44)
        | X44 != k7_enumset1(X35,X36,X37,X38,X39,X40,X41,X42,X43) )
      & ( X46 != X37
        | r2_hidden(X46,X44)
        | X44 != k7_enumset1(X35,X36,X37,X38,X39,X40,X41,X42,X43) )
      & ( X46 != X38
        | r2_hidden(X46,X44)
        | X44 != k7_enumset1(X35,X36,X37,X38,X39,X40,X41,X42,X43) )
      & ( X46 != X39
        | r2_hidden(X46,X44)
        | X44 != k7_enumset1(X35,X36,X37,X38,X39,X40,X41,X42,X43) )
      & ( X46 != X40
        | r2_hidden(X46,X44)
        | X44 != k7_enumset1(X35,X36,X37,X38,X39,X40,X41,X42,X43) )
      & ( X46 != X41
        | r2_hidden(X46,X44)
        | X44 != k7_enumset1(X35,X36,X37,X38,X39,X40,X41,X42,X43) )
      & ( X46 != X42
        | r2_hidden(X46,X44)
        | X44 != k7_enumset1(X35,X36,X37,X38,X39,X40,X41,X42,X43) )
      & ( X46 != X43
        | r2_hidden(X46,X44)
        | X44 != k7_enumset1(X35,X36,X37,X38,X39,X40,X41,X42,X43) )
      & ( esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56) != X47
        | ~ r2_hidden(esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56),X56)
        | X56 = k7_enumset1(X47,X48,X49,X50,X51,X52,X53,X54,X55) )
      & ( esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56) != X48
        | ~ r2_hidden(esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56),X56)
        | X56 = k7_enumset1(X47,X48,X49,X50,X51,X52,X53,X54,X55) )
      & ( esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56) != X49
        | ~ r2_hidden(esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56),X56)
        | X56 = k7_enumset1(X47,X48,X49,X50,X51,X52,X53,X54,X55) )
      & ( esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56) != X50
        | ~ r2_hidden(esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56),X56)
        | X56 = k7_enumset1(X47,X48,X49,X50,X51,X52,X53,X54,X55) )
      & ( esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56) != X51
        | ~ r2_hidden(esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56),X56)
        | X56 = k7_enumset1(X47,X48,X49,X50,X51,X52,X53,X54,X55) )
      & ( esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56) != X52
        | ~ r2_hidden(esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56),X56)
        | X56 = k7_enumset1(X47,X48,X49,X50,X51,X52,X53,X54,X55) )
      & ( esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56) != X53
        | ~ r2_hidden(esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56),X56)
        | X56 = k7_enumset1(X47,X48,X49,X50,X51,X52,X53,X54,X55) )
      & ( esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56) != X54
        | ~ r2_hidden(esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56),X56)
        | X56 = k7_enumset1(X47,X48,X49,X50,X51,X52,X53,X54,X55) )
      & ( esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56) != X55
        | ~ r2_hidden(esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56),X56)
        | X56 = k7_enumset1(X47,X48,X49,X50,X51,X52,X53,X54,X55) )
      & ( r2_hidden(esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56),X56)
        | esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56) = X47
        | esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56) = X48
        | esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56) = X49
        | esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56) = X50
        | esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56) = X51
        | esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56) = X52
        | esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56) = X53
        | esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56) = X54
        | esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56) = X55
        | X56 = k7_enumset1(X47,X48,X49,X50,X51,X52,X53,X54,X55) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_enumset1])])])])])])).

cnf(c_0_63,plain,
    ( X1 = X3
    | X2 != k5_enumset1(X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_64,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k5_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X8,X9),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X8,X9),k5_enumset1(X1,X1,X2,X3,X4,X5,X6)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_26]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_48]),c_0_48])).

cnf(c_0_65,negated_conjecture,
    ( k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) = k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_61]),c_0_40])).

cnf(c_0_66,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(spm,[status(thm)],[c_0_57,c_0_41])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k7_enumset1(X4,X5,X6,X7,X8,X2,X9,X10,X11) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_68,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,X2)
    | X2 != k7_enumset1(X3,X4,X5,X6,X7,X1,X8,X9,X10) ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( X1 = esk3_0
    | ~ r2_hidden(X1,k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,k7_enumset1(X2,X3,X4,X5,X6,X1,X7,X8,X9)) ),
    inference(er,[status(thm)],[c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73]),
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
% 0.13/0.34  % DateTime   : Tue Dec  1 11:02:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.19/0.40  # and selection function SelectNegativeLiterals.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.016 s
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.19/0.40  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.40  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.19/0.40  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.19/0.40  fof(t13_zfmisc_1, conjecture, ![X1, X2]:(k2_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 0.19/0.40  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.19/0.40  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.19/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.40  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.40  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.40  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.40  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.19/0.40  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.40  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.40  fof(t132_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_enumset1)).
% 0.19/0.40  fof(d7_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9, X10]:(X10=k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)<=>![X11]:(r2_hidden(X11,X10)<=>~(((((((((X11!=X1&X11!=X2)&X11!=X3)&X11!=X4)&X11!=X5)&X11!=X6)&X11!=X7)&X11!=X8)&X11!=X9)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_enumset1)).
% 0.19/0.40  fof(c_0_18, plain, ![X26, X27]:k2_xboole_0(X26,X27)=k5_xboole_0(X26,k4_xboole_0(X27,X26)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.19/0.40  fof(c_0_19, plain, ![X16, X17]:k4_xboole_0(X16,X17)=k5_xboole_0(X16,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.40  fof(c_0_20, plain, ![X20, X21]:k4_xboole_0(X20,k2_xboole_0(X20,X21))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.19/0.40  cnf(c_0_21, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.40  cnf(c_0_22, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  fof(c_0_23, plain, ![X18, X19]:k3_xboole_0(X18,k2_xboole_0(X18,X19))=X18, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.19/0.40  fof(c_0_24, negated_conjecture, ~(![X1, X2]:(k2_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2)), inference(assume_negation,[status(cth)],[t13_zfmisc_1])).
% 0.19/0.40  cnf(c_0_25, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_26, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.40  cnf(c_0_27, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.40  fof(c_0_28, plain, ![X22]:k5_xboole_0(X22,k1_xboole_0)=X22, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.19/0.40  fof(c_0_29, plain, ![X14, X15]:k5_xboole_0(X14,X15)=k5_xboole_0(X15,X14), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.19/0.40  fof(c_0_30, negated_conjecture, (k2_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0))=k1_tarski(esk3_0)&esk3_0!=esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 0.19/0.40  fof(c_0_31, plain, ![X67]:k2_tarski(X67,X67)=k1_tarski(X67), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.40  fof(c_0_32, plain, ![X68, X69]:k1_enumset1(X68,X68,X69)=k2_tarski(X68,X69), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.40  fof(c_0_33, plain, ![X70, X71, X72]:k2_enumset1(X70,X70,X71,X72)=k1_enumset1(X70,X71,X72), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.40  fof(c_0_34, plain, ![X73, X74, X75, X76]:k3_enumset1(X73,X73,X74,X75,X76)=k2_enumset1(X73,X74,X75,X76), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.40  fof(c_0_35, plain, ![X77, X78, X79, X80, X81]:k4_enumset1(X77,X77,X78,X79,X80,X81)=k3_enumset1(X77,X78,X79,X80,X81), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.40  fof(c_0_36, plain, ![X82, X83, X84, X85, X86, X87]:k5_enumset1(X82,X82,X83,X84,X85,X86,X87)=k4_enumset1(X82,X83,X84,X85,X86,X87), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.40  fof(c_0_37, plain, ![X23, X24, X25]:k5_xboole_0(k5_xboole_0(X23,X24),X25)=k5_xboole_0(X23,k5_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.19/0.40  cnf(c_0_38, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_22]), c_0_26])).
% 0.19/0.40  cnf(c_0_39, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=X1), inference(rw,[status(thm)],[c_0_27, c_0_26])).
% 0.19/0.40  cnf(c_0_40, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.40  cnf(c_0_41, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.40  cnf(c_0_42, negated_conjecture, (k2_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0))=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.40  cnf(c_0_43, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.40  cnf(c_0_44, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.40  cnf(c_0_45, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.40  cnf(c_0_46, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.40  cnf(c_0_47, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.40  cnf(c_0_48, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.40  fof(c_0_49, plain, ![X12, X13]:k3_xboole_0(X12,X13)=k3_xboole_0(X13,X12), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.40  cnf(c_0_50, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.40  cnf(c_0_51, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.40  cnf(c_0_52, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.40  cnf(c_0_53, negated_conjecture, (k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_44]), c_0_26]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48])).
% 0.19/0.40  cnf(c_0_54, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.40  fof(c_0_55, plain, ![X28, X29, X30, X31, X32, X33]:(((~r2_hidden(X30,X29)|X30=X28|X29!=k1_tarski(X28))&(X31!=X28|r2_hidden(X31,X29)|X29!=k1_tarski(X28)))&((~r2_hidden(esk1_2(X32,X33),X33)|esk1_2(X32,X33)!=X32|X33=k1_tarski(X32))&(r2_hidden(esk1_2(X32,X33),X33)|esk1_2(X32,X33)=X32|X33=k1_tarski(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.40  fof(c_0_56, plain, ![X58, X59, X60, X61, X62, X63, X64, X65, X66]:k7_enumset1(X58,X59,X60,X61,X62,X63,X64,X65,X66)=k2_xboole_0(k4_enumset1(X58,X59,X60,X61,X62,X63),k1_enumset1(X64,X65,X66)), inference(variable_rename,[status(thm)],[t132_enumset1])).
% 0.19/0.40  cnf(c_0_57, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.19/0.40  cnf(c_0_58, negated_conjecture, (k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))))=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.40  cnf(c_0_59, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.40  cnf(c_0_60, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.40  cnf(c_0_61, negated_conjecture, (k5_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_51])).
% 0.19/0.40  fof(c_0_62, plain, ![X35, X36, X37, X38, X39, X40, X41, X42, X43, X44, X45, X46, X47, X48, X49, X50, X51, X52, X53, X54, X55, X56]:(((~r2_hidden(X45,X44)|(X45=X35|X45=X36|X45=X37|X45=X38|X45=X39|X45=X40|X45=X41|X45=X42|X45=X43)|X44!=k7_enumset1(X35,X36,X37,X38,X39,X40,X41,X42,X43))&(((((((((X46!=X35|r2_hidden(X46,X44)|X44!=k7_enumset1(X35,X36,X37,X38,X39,X40,X41,X42,X43))&(X46!=X36|r2_hidden(X46,X44)|X44!=k7_enumset1(X35,X36,X37,X38,X39,X40,X41,X42,X43)))&(X46!=X37|r2_hidden(X46,X44)|X44!=k7_enumset1(X35,X36,X37,X38,X39,X40,X41,X42,X43)))&(X46!=X38|r2_hidden(X46,X44)|X44!=k7_enumset1(X35,X36,X37,X38,X39,X40,X41,X42,X43)))&(X46!=X39|r2_hidden(X46,X44)|X44!=k7_enumset1(X35,X36,X37,X38,X39,X40,X41,X42,X43)))&(X46!=X40|r2_hidden(X46,X44)|X44!=k7_enumset1(X35,X36,X37,X38,X39,X40,X41,X42,X43)))&(X46!=X41|r2_hidden(X46,X44)|X44!=k7_enumset1(X35,X36,X37,X38,X39,X40,X41,X42,X43)))&(X46!=X42|r2_hidden(X46,X44)|X44!=k7_enumset1(X35,X36,X37,X38,X39,X40,X41,X42,X43)))&(X46!=X43|r2_hidden(X46,X44)|X44!=k7_enumset1(X35,X36,X37,X38,X39,X40,X41,X42,X43))))&((((((((((esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56)!=X47|~r2_hidden(esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56),X56)|X56=k7_enumset1(X47,X48,X49,X50,X51,X52,X53,X54,X55))&(esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56)!=X48|~r2_hidden(esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56),X56)|X56=k7_enumset1(X47,X48,X49,X50,X51,X52,X53,X54,X55)))&(esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56)!=X49|~r2_hidden(esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56),X56)|X56=k7_enumset1(X47,X48,X49,X50,X51,X52,X53,X54,X55)))&(esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56)!=X50|~r2_hidden(esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56),X56)|X56=k7_enumset1(X47,X48,X49,X50,X51,X52,X53,X54,X55)))&(esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56)!=X51|~r2_hidden(esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56),X56)|X56=k7_enumset1(X47,X48,X49,X50,X51,X52,X53,X54,X55)))&(esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56)!=X52|~r2_hidden(esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56),X56)|X56=k7_enumset1(X47,X48,X49,X50,X51,X52,X53,X54,X55)))&(esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56)!=X53|~r2_hidden(esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56),X56)|X56=k7_enumset1(X47,X48,X49,X50,X51,X52,X53,X54,X55)))&(esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56)!=X54|~r2_hidden(esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56),X56)|X56=k7_enumset1(X47,X48,X49,X50,X51,X52,X53,X54,X55)))&(esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56)!=X55|~r2_hidden(esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56),X56)|X56=k7_enumset1(X47,X48,X49,X50,X51,X52,X53,X54,X55)))&(r2_hidden(esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56),X56)|(esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56)=X47|esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56)=X48|esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56)=X49|esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56)=X50|esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56)=X51|esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56)=X52|esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56)=X53|esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56)=X54|esk2_10(X47,X48,X49,X50,X51,X52,X53,X54,X55,X56)=X55)|X56=k7_enumset1(X47,X48,X49,X50,X51,X52,X53,X54,X55)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_enumset1])])])])])])).
% 0.19/0.40  cnf(c_0_63, plain, (X1=X3|X2!=k5_enumset1(X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47]), c_0_48])).
% 0.19/0.40  cnf(c_0_64, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k5_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X8,X9),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X8,X9),k5_enumset1(X1,X1,X2,X3,X4,X5,X6))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_26]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_48]), c_0_48])).
% 0.19/0.40  cnf(c_0_65, negated_conjecture, (k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))=k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_61]), c_0_40])).
% 0.19/0.40  cnf(c_0_66, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(spm,[status(thm)],[c_0_57, c_0_41])).
% 0.19/0.40  cnf(c_0_67, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k7_enumset1(X4,X5,X6,X7,X8,X2,X9,X10,X11)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.40  cnf(c_0_68, plain, (X1=X2|~r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_63])).
% 0.19/0.40  cnf(c_0_69, negated_conjecture, (k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])).
% 0.19/0.40  cnf(c_0_70, plain, (r2_hidden(X1,X2)|X2!=k7_enumset1(X3,X4,X5,X6,X7,X1,X8,X9,X10)), inference(er,[status(thm)],[c_0_67])).
% 0.19/0.40  cnf(c_0_71, negated_conjecture, (X1=esk3_0|~r2_hidden(X1,k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.19/0.40  cnf(c_0_72, plain, (r2_hidden(X1,k7_enumset1(X2,X3,X4,X5,X6,X1,X7,X8,X9))), inference(er,[status(thm)],[c_0_70])).
% 0.19/0.40  cnf(c_0_73, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.40  cnf(c_0_74, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 75
% 0.19/0.40  # Proof object clause steps            : 38
% 0.19/0.40  # Proof object formula steps           : 37
% 0.19/0.40  # Proof object conjectures             : 12
% 0.19/0.40  # Proof object clause conjectures      : 9
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 19
% 0.19/0.40  # Proof object initial formulas used   : 18
% 0.19/0.40  # Proof object generating inferences   : 10
% 0.19/0.40  # Proof object simplifying inferences  : 56
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 18
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 41
% 0.19/0.40  # Removed in clause preprocessing      : 8
% 0.19/0.40  # Initial clauses in saturation        : 33
% 0.19/0.40  # Processed clauses                    : 318
% 0.19/0.40  # ...of these trivial                  : 44
% 0.19/0.40  # ...subsumed                          : 169
% 0.19/0.40  # ...remaining for further processing  : 105
% 0.19/0.40  # Other redundant clauses eliminated   : 76
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 1
% 0.19/0.40  # Backward-rewritten                   : 5
% 0.19/0.40  # Generated clauses                    : 3158
% 0.19/0.40  # ...of the previous two non-trivial   : 2715
% 0.19/0.40  # Contextual simplify-reflections      : 0
% 0.19/0.40  # Paramodulations                      : 3055
% 0.19/0.40  # Factorizations                       : 8
% 0.19/0.40  # Equation resolutions                 : 95
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 89
% 0.19/0.40  #    Positive orientable unit clauses  : 36
% 0.19/0.40  #    Positive unorientable unit clauses: 5
% 0.19/0.40  #    Negative unit clauses             : 1
% 0.19/0.40  #    Non-unit-clauses                  : 47
% 0.19/0.40  # Current number of unprocessed clauses: 2422
% 0.19/0.40  # ...number of literals in the above   : 10489
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 14
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 283
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 246
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 16
% 0.19/0.40  # Unit Clause-clause subsumption calls : 20
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 137
% 0.19/0.40  # BW rewrite match successes           : 68
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 53167
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.051 s
% 0.19/0.40  # System time              : 0.010 s
% 0.19/0.40  # Total time               : 0.061 s
% 0.19/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
