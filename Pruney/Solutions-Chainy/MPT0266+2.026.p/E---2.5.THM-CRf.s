%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:42:12 EST 2020

% Result     : Theorem 0.61s
% Output     : CNFRefutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   83 (1266 expanded)
%              Number of clauses        :   44 ( 466 expanded)
%              Number of leaves         :   19 ( 399 expanded)
%              Depth                    :   12
%              Number of atoms          :  189 (1375 expanded)
%              Number of equality atoms :  134 (1317 expanded)
%              Maximal formula depth    :   52 (   4 average)
%              Maximal clause size      :   76 (   1 average)
%              Maximal term depth       :    6 (   2 average)

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

fof(t58_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(l142_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l142_enumset1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

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

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t63_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k3_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
     => r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_zfmisc_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t125_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(c_0_19,plain,(
    ! [X87,X88] : k3_tarski(k2_tarski(X87,X88)) = k2_xboole_0(X87,X88) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_20,plain,(
    ! [X65,X66] : k1_enumset1(X65,X65,X66) = k2_tarski(X65,X66) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X20,X21] : k3_xboole_0(X20,X21) = k5_xboole_0(k5_xboole_0(X20,X21),k2_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_22,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X67,X68,X69] : k2_enumset1(X67,X67,X68,X69) = k1_enumset1(X67,X68,X69) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_25,plain,(
    ! [X70,X71,X72,X73] : k3_enumset1(X70,X70,X71,X72,X73) = k2_enumset1(X70,X71,X72,X73) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_26,plain,(
    ! [X58,X59,X60,X61,X62,X63,X64] : k5_enumset1(X58,X59,X60,X61,X62,X63,X64) = k2_xboole_0(k1_enumset1(X58,X59,X60),k2_enumset1(X61,X62,X63,X64)) ),
    inference(variable_rename,[status(thm)],[t58_enumset1])).

fof(c_0_27,plain,(
    ! [X74,X75,X76,X77,X78] : k4_enumset1(X74,X74,X75,X76,X77,X78) = k3_enumset1(X74,X75,X76,X77,X78) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_28,plain,(
    ! [X79,X80,X81,X82,X83,X84] : k5_enumset1(X79,X79,X80,X81,X82,X83,X84) = k4_enumset1(X79,X80,X81,X82,X83,X84) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_29,plain,(
    ! [X45,X46,X47,X48,X49,X50,X51,X52,X53] : k7_enumset1(X45,X46,X47,X48,X49,X50,X51,X52,X53) = k2_xboole_0(k2_enumset1(X45,X46,X47,X48),k3_enumset1(X49,X50,X51,X52,X53)) ),
    inference(variable_rename,[status(thm)],[l142_enumset1])).

fof(c_0_30,plain,(
    ! [X15] : k3_xboole_0(X15,X15) = X15 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_35,plain,(
    ! [X14] : k2_xboole_0(X14,X14) = X14 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_36,plain,(
    ! [X22,X23,X24,X25,X26,X27,X28,X29,X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40,X41,X42,X43] :
      ( ( ~ r2_hidden(X32,X31)
        | X32 = X22
        | X32 = X23
        | X32 = X24
        | X32 = X25
        | X32 = X26
        | X32 = X27
        | X32 = X28
        | X32 = X29
        | X32 = X30
        | X31 != k7_enumset1(X22,X23,X24,X25,X26,X27,X28,X29,X30) )
      & ( X33 != X22
        | r2_hidden(X33,X31)
        | X31 != k7_enumset1(X22,X23,X24,X25,X26,X27,X28,X29,X30) )
      & ( X33 != X23
        | r2_hidden(X33,X31)
        | X31 != k7_enumset1(X22,X23,X24,X25,X26,X27,X28,X29,X30) )
      & ( X33 != X24
        | r2_hidden(X33,X31)
        | X31 != k7_enumset1(X22,X23,X24,X25,X26,X27,X28,X29,X30) )
      & ( X33 != X25
        | r2_hidden(X33,X31)
        | X31 != k7_enumset1(X22,X23,X24,X25,X26,X27,X28,X29,X30) )
      & ( X33 != X26
        | r2_hidden(X33,X31)
        | X31 != k7_enumset1(X22,X23,X24,X25,X26,X27,X28,X29,X30) )
      & ( X33 != X27
        | r2_hidden(X33,X31)
        | X31 != k7_enumset1(X22,X23,X24,X25,X26,X27,X28,X29,X30) )
      & ( X33 != X28
        | r2_hidden(X33,X31)
        | X31 != k7_enumset1(X22,X23,X24,X25,X26,X27,X28,X29,X30) )
      & ( X33 != X29
        | r2_hidden(X33,X31)
        | X31 != k7_enumset1(X22,X23,X24,X25,X26,X27,X28,X29,X30) )
      & ( X33 != X30
        | r2_hidden(X33,X31)
        | X31 != k7_enumset1(X22,X23,X24,X25,X26,X27,X28,X29,X30) )
      & ( esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43) != X34
        | ~ r2_hidden(esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43),X43)
        | X43 = k7_enumset1(X34,X35,X36,X37,X38,X39,X40,X41,X42) )
      & ( esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43) != X35
        | ~ r2_hidden(esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43),X43)
        | X43 = k7_enumset1(X34,X35,X36,X37,X38,X39,X40,X41,X42) )
      & ( esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43) != X36
        | ~ r2_hidden(esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43),X43)
        | X43 = k7_enumset1(X34,X35,X36,X37,X38,X39,X40,X41,X42) )
      & ( esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43) != X37
        | ~ r2_hidden(esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43),X43)
        | X43 = k7_enumset1(X34,X35,X36,X37,X38,X39,X40,X41,X42) )
      & ( esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43) != X38
        | ~ r2_hidden(esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43),X43)
        | X43 = k7_enumset1(X34,X35,X36,X37,X38,X39,X40,X41,X42) )
      & ( esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43) != X39
        | ~ r2_hidden(esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43),X43)
        | X43 = k7_enumset1(X34,X35,X36,X37,X38,X39,X40,X41,X42) )
      & ( esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43) != X40
        | ~ r2_hidden(esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43),X43)
        | X43 = k7_enumset1(X34,X35,X36,X37,X38,X39,X40,X41,X42) )
      & ( esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43) != X41
        | ~ r2_hidden(esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43),X43)
        | X43 = k7_enumset1(X34,X35,X36,X37,X38,X39,X40,X41,X42) )
      & ( esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43) != X42
        | ~ r2_hidden(esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43),X43)
        | X43 = k7_enumset1(X34,X35,X36,X37,X38,X39,X40,X41,X42) )
      & ( r2_hidden(esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43),X43)
        | esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43) = X34
        | esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43) = X35
        | esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43) = X36
        | esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43) = X37
        | esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43) = X38
        | esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43) = X39
        | esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43) = X40
        | esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43) = X41
        | esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43) = X42
        | X43 = k7_enumset1(X34,X35,X36,X37,X38,X39,X40,X41,X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_enumset1])])])])])])).

cnf(c_0_37,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])).

fof(c_0_43,plain,(
    ! [X19] : k5_xboole_0(X19,X19) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_45,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k3_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
       => r2_hidden(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t63_zfmisc_1])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k7_enumset1(X4,X5,X6,X7,X8,X9,X10,X11,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X4,X4,X4,X4,X5,X6,X7))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_32]),c_0_33]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39])).

cnf(c_0_48,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X6,X7,X8,X9))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_32]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39])).

fof(c_0_49,plain,(
    ! [X16,X17,X18] : k5_xboole_0(k5_xboole_0(X16,X17),X18) = k5_xboole_0(X16,k5_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_50,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_38]),c_0_39])).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_32]),c_0_33]),c_0_34]),c_0_38]),c_0_39])).

fof(c_0_53,negated_conjecture,
    ( k3_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0) = k2_tarski(esk2_0,esk3_0)
    & ~ r2_hidden(esk2_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_45])])])).

fof(c_0_54,plain,(
    ! [X54,X55,X56,X57] : k2_enumset1(X54,X55,X56,X57) = k2_enumset1(X57,X56,X55,X54) ),
    inference(variable_rename,[status(thm)],[t125_enumset1])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X2)
    | X2 != k7_enumset1(X3,X4,X5,X6,X7,X8,X9,X10,X1) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_56,plain,
    ( k7_enumset1(X1,X1,X2,X3,X4,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_57,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_58,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

fof(c_0_59,plain,(
    ! [X12,X13] : k5_xboole_0(X12,X13) = k5_xboole_0(X13,X12) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_60,negated_conjecture,
    ( k3_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0) = k2_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_61,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_62,plain,(
    ! [X85,X86] :
      ( ~ r2_hidden(X85,X86)
      | r1_tarski(X85,k3_tarski(X86)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X2)
    | X2 != k5_enumset1(X3,X4,X5,X6,X7,X8,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_64,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_51]),c_0_58])).

cnf(c_0_65,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),esk4_0),k3_tarski(k5_enumset1(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),esk4_0))) = k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_23]),c_0_23]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_42]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39])).

cnf(c_0_67,plain,
    ( k5_enumset1(X1,X1,X1,X1,X2,X3,X4) = k5_enumset1(X4,X4,X4,X4,X3,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_34]),c_0_34]),c_0_38]),c_0_38]),c_0_39]),c_0_39])).

fof(c_0_68,plain,(
    ! [X89,X90,X91] :
      ( ( r2_hidden(X89,X91)
        | ~ r1_tarski(k2_tarski(X89,X90),X91) )
      & ( r2_hidden(X90,X91)
        | ~ r1_tarski(k2_tarski(X89,X90),X91) )
      & ( ~ r2_hidden(X89,X91)
        | ~ r2_hidden(X90,X91)
        | r1_tarski(k2_tarski(X89,X90),X91) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,k5_enumset1(X2,X3,X4,X5,X6,X7,X1)) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_71,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( k5_xboole_0(esk4_0,k5_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k3_tarski(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0))))) = k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_65]),c_0_67]),c_0_57])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,k3_tarski(k5_enumset1(X2,X3,X4,X5,X6,X7,X1))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( k3_tarski(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0))) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_57]),c_0_71])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_23]),c_0_33]),c_0_34]),c_0_38]),c_0_39])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,k3_tarski(k7_enumset1(X2,X2,X3,X4,X5,X5,X6,X7,X1))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_56])).

cnf(c_0_78,negated_conjecture,
    ( k3_tarski(k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,k7_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k7_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k7_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0))) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_56]),c_0_56]),c_0_56]),c_0_56])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k7_enumset1(X1,X1,X1,X1,X1,X1,X1,X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_76,c_0_56])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(k7_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:11:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.61/0.86  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.61/0.86  # and selection function SelectNegativeLiterals.
% 0.61/0.86  #
% 0.61/0.86  # Preprocessing time       : 0.028 s
% 0.61/0.86  
% 0.61/0.86  # Proof found!
% 0.61/0.86  # SZS status Theorem
% 0.61/0.86  # SZS output start CNFRefutation
% 0.61/0.86  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.61/0.86  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.61/0.86  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.61/0.86  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.61/0.86  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.61/0.86  fof(t58_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_enumset1)).
% 0.61/0.86  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.61/0.86  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.61/0.86  fof(l142_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l142_enumset1)).
% 0.61/0.86  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.61/0.86  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.61/0.86  fof(d7_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9, X10]:(X10=k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)<=>![X11]:(r2_hidden(X11,X10)<=>~(((((((((X11!=X1&X11!=X2)&X11!=X3)&X11!=X4)&X11!=X5)&X11!=X6)&X11!=X7)&X11!=X8)&X11!=X9)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_enumset1)).
% 0.61/0.86  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.61/0.86  fof(t63_zfmisc_1, conjecture, ![X1, X2, X3]:(k3_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)=>r2_hidden(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 0.61/0.86  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.61/0.86  fof(t125_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 0.61/0.86  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.61/0.86  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.61/0.86  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.61/0.86  fof(c_0_19, plain, ![X87, X88]:k3_tarski(k2_tarski(X87,X88))=k2_xboole_0(X87,X88), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.61/0.86  fof(c_0_20, plain, ![X65, X66]:k1_enumset1(X65,X65,X66)=k2_tarski(X65,X66), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.61/0.86  fof(c_0_21, plain, ![X20, X21]:k3_xboole_0(X20,X21)=k5_xboole_0(k5_xboole_0(X20,X21),k2_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.61/0.86  cnf(c_0_22, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.61/0.86  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.61/0.86  fof(c_0_24, plain, ![X67, X68, X69]:k2_enumset1(X67,X67,X68,X69)=k1_enumset1(X67,X68,X69), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.61/0.86  fof(c_0_25, plain, ![X70, X71, X72, X73]:k3_enumset1(X70,X70,X71,X72,X73)=k2_enumset1(X70,X71,X72,X73), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.61/0.86  fof(c_0_26, plain, ![X58, X59, X60, X61, X62, X63, X64]:k5_enumset1(X58,X59,X60,X61,X62,X63,X64)=k2_xboole_0(k1_enumset1(X58,X59,X60),k2_enumset1(X61,X62,X63,X64)), inference(variable_rename,[status(thm)],[t58_enumset1])).
% 0.61/0.86  fof(c_0_27, plain, ![X74, X75, X76, X77, X78]:k4_enumset1(X74,X74,X75,X76,X77,X78)=k3_enumset1(X74,X75,X76,X77,X78), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.61/0.86  fof(c_0_28, plain, ![X79, X80, X81, X82, X83, X84]:k5_enumset1(X79,X79,X80,X81,X82,X83,X84)=k4_enumset1(X79,X80,X81,X82,X83,X84), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.61/0.86  fof(c_0_29, plain, ![X45, X46, X47, X48, X49, X50, X51, X52, X53]:k7_enumset1(X45,X46,X47,X48,X49,X50,X51,X52,X53)=k2_xboole_0(k2_enumset1(X45,X46,X47,X48),k3_enumset1(X49,X50,X51,X52,X53)), inference(variable_rename,[status(thm)],[l142_enumset1])).
% 0.61/0.86  fof(c_0_30, plain, ![X15]:k3_xboole_0(X15,X15)=X15, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.61/0.86  cnf(c_0_31, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.61/0.86  cnf(c_0_32, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.61/0.86  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.61/0.86  cnf(c_0_34, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.61/0.86  fof(c_0_35, plain, ![X14]:k2_xboole_0(X14,X14)=X14, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.61/0.86  fof(c_0_36, plain, ![X22, X23, X24, X25, X26, X27, X28, X29, X30, X31, X32, X33, X34, X35, X36, X37, X38, X39, X40, X41, X42, X43]:(((~r2_hidden(X32,X31)|(X32=X22|X32=X23|X32=X24|X32=X25|X32=X26|X32=X27|X32=X28|X32=X29|X32=X30)|X31!=k7_enumset1(X22,X23,X24,X25,X26,X27,X28,X29,X30))&(((((((((X33!=X22|r2_hidden(X33,X31)|X31!=k7_enumset1(X22,X23,X24,X25,X26,X27,X28,X29,X30))&(X33!=X23|r2_hidden(X33,X31)|X31!=k7_enumset1(X22,X23,X24,X25,X26,X27,X28,X29,X30)))&(X33!=X24|r2_hidden(X33,X31)|X31!=k7_enumset1(X22,X23,X24,X25,X26,X27,X28,X29,X30)))&(X33!=X25|r2_hidden(X33,X31)|X31!=k7_enumset1(X22,X23,X24,X25,X26,X27,X28,X29,X30)))&(X33!=X26|r2_hidden(X33,X31)|X31!=k7_enumset1(X22,X23,X24,X25,X26,X27,X28,X29,X30)))&(X33!=X27|r2_hidden(X33,X31)|X31!=k7_enumset1(X22,X23,X24,X25,X26,X27,X28,X29,X30)))&(X33!=X28|r2_hidden(X33,X31)|X31!=k7_enumset1(X22,X23,X24,X25,X26,X27,X28,X29,X30)))&(X33!=X29|r2_hidden(X33,X31)|X31!=k7_enumset1(X22,X23,X24,X25,X26,X27,X28,X29,X30)))&(X33!=X30|r2_hidden(X33,X31)|X31!=k7_enumset1(X22,X23,X24,X25,X26,X27,X28,X29,X30))))&((((((((((esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43)!=X34|~r2_hidden(esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43),X43)|X43=k7_enumset1(X34,X35,X36,X37,X38,X39,X40,X41,X42))&(esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43)!=X35|~r2_hidden(esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43),X43)|X43=k7_enumset1(X34,X35,X36,X37,X38,X39,X40,X41,X42)))&(esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43)!=X36|~r2_hidden(esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43),X43)|X43=k7_enumset1(X34,X35,X36,X37,X38,X39,X40,X41,X42)))&(esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43)!=X37|~r2_hidden(esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43),X43)|X43=k7_enumset1(X34,X35,X36,X37,X38,X39,X40,X41,X42)))&(esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43)!=X38|~r2_hidden(esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43),X43)|X43=k7_enumset1(X34,X35,X36,X37,X38,X39,X40,X41,X42)))&(esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43)!=X39|~r2_hidden(esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43),X43)|X43=k7_enumset1(X34,X35,X36,X37,X38,X39,X40,X41,X42)))&(esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43)!=X40|~r2_hidden(esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43),X43)|X43=k7_enumset1(X34,X35,X36,X37,X38,X39,X40,X41,X42)))&(esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43)!=X41|~r2_hidden(esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43),X43)|X43=k7_enumset1(X34,X35,X36,X37,X38,X39,X40,X41,X42)))&(esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43)!=X42|~r2_hidden(esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43),X43)|X43=k7_enumset1(X34,X35,X36,X37,X38,X39,X40,X41,X42)))&(r2_hidden(esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43),X43)|(esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43)=X34|esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43)=X35|esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43)=X36|esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43)=X37|esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43)=X38|esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43)=X39|esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43)=X40|esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43)=X41|esk1_10(X34,X35,X36,X37,X38,X39,X40,X41,X42,X43)=X42)|X43=k7_enumset1(X34,X35,X36,X37,X38,X39,X40,X41,X42)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_enumset1])])])])])])).
% 0.61/0.86  cnf(c_0_37, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.61/0.86  cnf(c_0_38, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.61/0.86  cnf(c_0_39, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.61/0.86  cnf(c_0_40, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.61/0.86  cnf(c_0_41, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.61/0.86  cnf(c_0_42, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])).
% 0.61/0.86  fof(c_0_43, plain, ![X19]:k5_xboole_0(X19,X19)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.61/0.86  cnf(c_0_44, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.61/0.86  fof(c_0_45, negated_conjecture, ~(![X1, X2, X3]:(k3_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)=>r2_hidden(X1,X3))), inference(assume_negation,[status(cth)],[t63_zfmisc_1])).
% 0.61/0.86  cnf(c_0_46, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k7_enumset1(X4,X5,X6,X7,X8,X9,X10,X11,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.61/0.86  cnf(c_0_47, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X4,X4,X4,X4,X5,X6,X7)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_32]), c_0_33]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39])).
% 0.61/0.86  cnf(c_0_48, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X6,X7,X8,X9)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_32]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39])).
% 0.61/0.86  fof(c_0_49, plain, ![X16, X17, X18]:k5_xboole_0(k5_xboole_0(X16,X17),X18)=k5_xboole_0(X16,k5_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.61/0.86  cnf(c_0_50, plain, (k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_38]), c_0_39])).
% 0.61/0.86  cnf(c_0_51, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.61/0.86  cnf(c_0_52, plain, (k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_32]), c_0_33]), c_0_34]), c_0_38]), c_0_39])).
% 0.61/0.86  fof(c_0_53, negated_conjecture, (k3_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0)=k2_tarski(esk2_0,esk3_0)&~r2_hidden(esk2_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_45])])])).
% 0.61/0.86  fof(c_0_54, plain, ![X54, X55, X56, X57]:k2_enumset1(X54,X55,X56,X57)=k2_enumset1(X57,X56,X55,X54), inference(variable_rename,[status(thm)],[t125_enumset1])).
% 0.61/0.86  cnf(c_0_55, plain, (r2_hidden(X1,X2)|X2!=k7_enumset1(X3,X4,X5,X6,X7,X8,X9,X10,X1)), inference(er,[status(thm)],[c_0_46])).
% 0.61/0.86  cnf(c_0_56, plain, (k7_enumset1(X1,X1,X2,X3,X4,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 0.61/0.86  cnf(c_0_57, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.61/0.86  cnf(c_0_58, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.61/0.86  fof(c_0_59, plain, ![X12, X13]:k5_xboole_0(X12,X13)=k5_xboole_0(X13,X12), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.61/0.86  cnf(c_0_60, negated_conjecture, (k3_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0)=k2_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.61/0.86  cnf(c_0_61, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.61/0.86  fof(c_0_62, plain, ![X85, X86]:(~r2_hidden(X85,X86)|r1_tarski(X85,k3_tarski(X86))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.61/0.86  cnf(c_0_63, plain, (r2_hidden(X1,X2)|X2!=k5_enumset1(X3,X4,X5,X6,X7,X8,X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.61/0.86  cnf(c_0_64, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_51]), c_0_58])).
% 0.61/0.86  cnf(c_0_65, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.61/0.86  cnf(c_0_66, negated_conjecture, (k5_xboole_0(k5_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),esk4_0),k3_tarski(k5_enumset1(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),esk4_0)))=k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_23]), c_0_23]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_42]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39])).
% 0.61/0.86  cnf(c_0_67, plain, (k5_enumset1(X1,X1,X1,X1,X2,X3,X4)=k5_enumset1(X4,X4,X4,X4,X3,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_34]), c_0_34]), c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 0.61/0.86  fof(c_0_68, plain, ![X89, X90, X91]:(((r2_hidden(X89,X91)|~r1_tarski(k2_tarski(X89,X90),X91))&(r2_hidden(X90,X91)|~r1_tarski(k2_tarski(X89,X90),X91)))&(~r2_hidden(X89,X91)|~r2_hidden(X90,X91)|r1_tarski(k2_tarski(X89,X90),X91))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.61/0.86  cnf(c_0_69, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.61/0.86  cnf(c_0_70, plain, (r2_hidden(X1,k5_enumset1(X2,X3,X4,X5,X6,X7,X1))), inference(er,[status(thm)],[c_0_63])).
% 0.61/0.86  cnf(c_0_71, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.61/0.86  cnf(c_0_72, negated_conjecture, (k5_xboole_0(esk4_0,k5_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k3_tarski(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)))))=k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_65]), c_0_67]), c_0_57])).
% 0.61/0.86  cnf(c_0_73, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.61/0.86  cnf(c_0_74, plain, (r1_tarski(X1,k3_tarski(k5_enumset1(X2,X3,X4,X5,X6,X7,X1)))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.61/0.86  cnf(c_0_75, negated_conjecture, (k3_tarski(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)))=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_57]), c_0_71])).
% 0.61/0.86  cnf(c_0_76, plain, (r2_hidden(X1,X2)|~r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_23]), c_0_33]), c_0_34]), c_0_38]), c_0_39])).
% 0.61/0.86  cnf(c_0_77, plain, (r1_tarski(X1,k3_tarski(k7_enumset1(X2,X2,X3,X4,X5,X5,X6,X7,X1)))), inference(spm,[status(thm)],[c_0_74, c_0_56])).
% 0.61/0.86  cnf(c_0_78, negated_conjecture, (k3_tarski(k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,k7_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k7_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k7_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)))=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_56]), c_0_56]), c_0_56]), c_0_56])).
% 0.61/0.86  cnf(c_0_79, plain, (r2_hidden(X1,X2)|~r1_tarski(k7_enumset1(X1,X1,X1,X1,X1,X1,X1,X1,X3),X2)), inference(spm,[status(thm)],[c_0_76, c_0_56])).
% 0.61/0.86  cnf(c_0_80, negated_conjecture, (r1_tarski(k7_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.61/0.86  cnf(c_0_81, negated_conjecture, (~r2_hidden(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.61/0.86  cnf(c_0_82, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81]), ['proof']).
% 0.61/0.86  # SZS output end CNFRefutation
% 0.61/0.86  # Proof object total steps             : 83
% 0.61/0.86  # Proof object clause steps            : 44
% 0.61/0.86  # Proof object formula steps           : 39
% 0.61/0.86  # Proof object conjectures             : 11
% 0.61/0.86  # Proof object clause conjectures      : 8
% 0.61/0.86  # Proof object formula conjectures     : 3
% 0.61/0.86  # Proof object initial clauses used    : 20
% 0.61/0.86  # Proof object initial formulas used   : 19
% 0.61/0.86  # Proof object generating inferences   : 10
% 0.61/0.86  # Proof object simplifying inferences  : 101
% 0.61/0.86  # Training examples: 0 positive, 0 negative
% 0.61/0.86  # Parsed axioms                        : 19
% 0.61/0.86  # Removed by relevancy pruning/SinE    : 0
% 0.61/0.86  # Initial clauses                      : 41
% 0.61/0.86  # Removed in clause preprocessing      : 7
% 0.61/0.86  # Initial clauses in saturation        : 34
% 0.61/0.86  # Processed clauses                    : 1190
% 0.61/0.86  # ...of these trivial                  : 240
% 0.61/0.86  # ...subsumed                          : 795
% 0.61/0.86  # ...remaining for further processing  : 155
% 0.61/0.86  # Other redundant clauses eliminated   : 468
% 0.61/0.86  # Clauses deleted for lack of memory   : 0
% 0.61/0.86  # Backward-subsumed                    : 0
% 0.61/0.86  # Backward-rewritten                   : 3
% 0.61/0.86  # Generated clauses                    : 4161
% 0.61/0.86  # ...of the previous two non-trivial   : 3088
% 0.61/0.86  # Contextual simplify-reflections      : 0
% 0.61/0.86  # Paramodulations                      : 3365
% 0.61/0.86  # Factorizations                       : 306
% 0.61/0.86  # Equation resolutions                 : 490
% 0.61/0.86  # Propositional unsat checks           : 0
% 0.61/0.86  #    Propositional check models        : 0
% 0.61/0.86  #    Propositional check unsatisfiable : 0
% 0.61/0.86  #    Propositional clauses             : 0
% 0.61/0.86  #    Propositional clauses after purity: 0
% 0.61/0.86  #    Propositional unsat core size     : 0
% 0.61/0.86  #    Propositional preprocessing time  : 0.000
% 0.61/0.86  #    Propositional encoding time       : 0.000
% 0.61/0.86  #    Propositional solver time         : 0.000
% 0.61/0.86  #    Success case prop preproc time    : 0.000
% 0.61/0.86  #    Success case prop encoding time   : 0.000
% 0.61/0.86  #    Success case prop solver time     : 0.000
% 0.61/0.86  # Current number of processed clauses  : 143
% 0.61/0.86  #    Positive orientable unit clauses  : 48
% 0.61/0.86  #    Positive unorientable unit clauses: 18
% 0.61/0.86  #    Negative unit clauses             : 1
% 0.61/0.86  #    Non-unit-clauses                  : 76
% 0.61/0.86  # Current number of unprocessed clauses: 1912
% 0.61/0.86  # ...number of literals in the above   : 14277
% 0.61/0.86  # Current number of archived formulas  : 0
% 0.61/0.86  # Current number of archived clauses   : 10
% 0.61/0.86  # Clause-clause subsumption calls (NU) : 5554
% 0.61/0.86  # Rec. Clause-clause subsumption calls : 5507
% 0.61/0.86  # Non-unit clause-clause subsumptions  : 560
% 0.61/0.86  # Unit Clause-clause subsumption calls : 128
% 0.61/0.86  # Rewrite failures with RHS unbound    : 0
% 0.61/0.86  # BW rewrite match attempts            : 1212
% 0.61/0.86  # BW rewrite match successes           : 440
% 0.61/0.86  # Condensation attempts                : 0
% 0.61/0.86  # Condensation successes               : 0
% 0.61/0.86  # Termbank termtop insertions          : 63230
% 0.61/0.86  
% 0.61/0.86  # -------------------------------------------------
% 0.61/0.86  # User time                : 0.513 s
% 0.61/0.86  # System time              : 0.008 s
% 0.61/0.86  # Total time               : 0.521 s
% 0.61/0.86  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
