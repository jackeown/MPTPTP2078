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
% DateTime   : Thu Dec  3 10:40:16 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 480 expanded)
%              Number of clauses        :   49 ( 180 expanded)
%              Number of leaves         :   24 ( 149 expanded)
%              Depth                    :   10
%              Number of atoms          :  168 ( 553 expanded)
%              Number of equality atoms :   96 ( 475 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t45_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)
     => r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(t61_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

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

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t67_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

fof(t102_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_enumset1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(l97_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(l24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(c_0_24,plain,(
    ! [X87,X88] : k3_tarski(k2_tarski(X87,X88)) = k2_xboole_0(X87,X88) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_25,plain,(
    ! [X58,X59] : k1_enumset1(X58,X58,X59) = k2_tarski(X58,X59) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)
       => r2_hidden(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t45_zfmisc_1])).

fof(c_0_27,plain,(
    ! [X42,X43,X44,X45,X46,X47,X48] : k5_enumset1(X42,X43,X44,X45,X46,X47,X48) = k2_xboole_0(k4_enumset1(X42,X43,X44,X45,X46,X47),k1_tarski(X48)) ),
    inference(variable_rename,[status(thm)],[t61_enumset1])).

fof(c_0_28,plain,(
    ! [X57] : k2_tarski(X57,X57) = k1_tarski(X57) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_29,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_31,plain,(
    ! [X60,X61,X62] : k2_enumset1(X60,X60,X61,X62) = k1_enumset1(X60,X61,X62) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_32,plain,(
    ! [X63,X64,X65,X66] : k3_enumset1(X63,X63,X64,X65,X66) = k2_enumset1(X63,X64,X65,X66) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_33,plain,(
    ! [X67,X68,X69,X70,X71] : k4_enumset1(X67,X67,X68,X69,X70,X71) = k3_enumset1(X67,X68,X69,X70,X71) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_34,plain,(
    ! [X72,X73,X74,X75,X76,X77] : k5_enumset1(X72,X72,X73,X74,X75,X76,X77) = k4_enumset1(X72,X73,X74,X75,X76,X77) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_35,plain,(
    ! [X78,X79,X80,X81,X82,X83,X84] : k6_enumset1(X78,X78,X79,X80,X81,X82,X83,X84) = k5_enumset1(X78,X79,X80,X81,X82,X83,X84) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_36,plain,(
    ! [X49,X50,X51,X52,X53,X54,X55,X56] : k6_enumset1(X49,X50,X51,X52,X53,X54,X55,X56) = k2_xboole_0(k4_enumset1(X49,X50,X51,X52,X53,X54),k2_tarski(X55,X56)) ),
    inference(variable_rename,[status(thm)],[t67_enumset1])).

fof(c_0_37,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(esk2_0),esk3_0),esk3_0)
    & ~ r2_hidden(esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

fof(c_0_38,plain,(
    ! [X39,X40,X41] : k1_enumset1(X39,X40,X41) = k1_enumset1(X41,X40,X39) ),
    inference(variable_rename,[status(thm)],[t102_enumset1])).

cnf(c_0_39,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_42,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_48,plain,(
    ! [X26,X27] : k3_xboole_0(X26,X27) = k5_xboole_0(k5_xboole_0(X26,X27),k2_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

fof(c_0_49,plain,(
    ! [X28,X29,X30,X31,X32,X33,X34,X35,X36,X37] :
      ( ( ~ r2_hidden(X32,X31)
        | X32 = X28
        | X32 = X29
        | X32 = X30
        | X31 != k1_enumset1(X28,X29,X30) )
      & ( X33 != X28
        | r2_hidden(X33,X31)
        | X31 != k1_enumset1(X28,X29,X30) )
      & ( X33 != X29
        | r2_hidden(X33,X31)
        | X31 != k1_enumset1(X28,X29,X30) )
      & ( X33 != X30
        | r2_hidden(X33,X31)
        | X31 != k1_enumset1(X28,X29,X30) )
      & ( esk1_4(X34,X35,X36,X37) != X34
        | ~ r2_hidden(esk1_4(X34,X35,X36,X37),X37)
        | X37 = k1_enumset1(X34,X35,X36) )
      & ( esk1_4(X34,X35,X36,X37) != X35
        | ~ r2_hidden(esk1_4(X34,X35,X36,X37),X37)
        | X37 = k1_enumset1(X34,X35,X36) )
      & ( esk1_4(X34,X35,X36,X37) != X36
        | ~ r2_hidden(esk1_4(X34,X35,X36,X37),X37)
        | X37 = k1_enumset1(X34,X35,X36) )
      & ( r2_hidden(esk1_4(X34,X35,X36,X37),X37)
        | esk1_4(X34,X35,X36,X37) = X34
        | esk1_4(X34,X35,X36,X37) = X35
        | esk1_4(X34,X35,X36,X37) = X36
        | X37 = k1_enumset1(X34,X35,X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(esk2_0),esk3_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40]),c_0_30]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46])).

cnf(c_0_53,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_30]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46])).

fof(c_0_54,plain,(
    ! [X12] : k3_xboole_0(X12,X12) = X12 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_56,plain,(
    ! [X11] : k2_xboole_0(X11,X11) = X11 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_58,plain,(
    ! [X18,X19] : r1_xboole_0(k3_xboole_0(X18,X19),k5_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[l97_xboole_1])).

fof(c_0_59,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_40]),c_0_30]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46])).

cnf(c_0_61,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_46])).

cnf(c_0_62,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X7) = k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[c_0_52,c_0_53])).

fof(c_0_63,plain,(
    ! [X20,X21] : r1_tarski(X20,k2_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_64,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_65,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_41]),c_0_42]),c_0_43])).

fof(c_0_66,plain,(
    ! [X25] : k5_xboole_0(X25,X25) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_67,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_68,plain,(
    ! [X85,X86] :
      ( ~ r1_xboole_0(k1_tarski(X85),X86)
      | ~ r2_hidden(X85,X86) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

fof(c_0_69,plain,(
    ! [X13,X14,X15] :
      ( ( ~ r2_hidden(X13,X14)
        | ~ r2_hidden(X13,X15)
        | ~ r2_hidden(X13,k5_xboole_0(X14,X15)) )
      & ( r2_hidden(X13,X14)
        | r2_hidden(X13,X15)
        | ~ r2_hidden(X13,k5_xboole_0(X14,X15)) )
      & ( ~ r2_hidden(X13,X14)
        | r2_hidden(X13,X15)
        | r2_hidden(X13,k5_xboole_0(X14,X15)) )
      & ( ~ r2_hidden(X13,X15)
        | r2_hidden(X13,X14)
        | r2_hidden(X13,k5_xboole_0(X14,X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_71,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_72,plain,(
    ! [X22,X23,X24] : k5_xboole_0(k5_xboole_0(X22,X23),X24) = k5_xboole_0(X22,k5_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_73,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_75,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_76,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_77,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_78,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_79,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_80,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X3,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_81,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_70])])).

cnf(c_0_82,plain,
    ( r1_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_65]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_83,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_84,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))) = esk3_0
    | ~ r1_tarski(esk3_0,k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_85,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

fof(c_0_86,plain,(
    ! [X9,X10] : k5_xboole_0(X9,X10) = k5_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_87,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77]),c_0_78])).

cnf(c_0_88,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_40]),c_0_30]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_89,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X1)))
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_90,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_91,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_85])])).

cnf(c_0_92,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_93,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_77]),c_0_87])).

cnf(c_0_94,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X1))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_95,negated_conjecture,
    ( r1_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(esk3_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_92]),c_0_93])).

cnf(c_0_96,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:31:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 2.76/2.93  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 2.76/2.93  # and selection function GSelectMinInfpos.
% 2.76/2.93  #
% 2.76/2.93  # Preprocessing time       : 0.027 s
% 2.76/2.93  # Presaturation interreduction done
% 2.76/2.93  
% 2.76/2.93  # Proof found!
% 2.76/2.93  # SZS status Theorem
% 2.76/2.93  # SZS output start CNFRefutation
% 2.76/2.93  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.76/2.93  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.76/2.93  fof(t45_zfmisc_1, conjecture, ![X1, X2]:(r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.76/2.93  fof(t61_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_enumset1)).
% 2.76/2.93  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.76/2.93  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.76/2.93  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.76/2.93  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.76/2.93  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.76/2.93  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 2.76/2.93  fof(t67_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_enumset1)).
% 2.76/2.93  fof(t102_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X3,X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_enumset1)).
% 2.76/2.93  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 2.76/2.93  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.76/2.93  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.76/2.93  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.76/2.93  fof(l97_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 2.76/2.93  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.76/2.93  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.76/2.93  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.76/2.93  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.76/2.93  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.76/2.93  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 2.76/2.93  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.76/2.93  fof(c_0_24, plain, ![X87, X88]:k3_tarski(k2_tarski(X87,X88))=k2_xboole_0(X87,X88), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 2.76/2.93  fof(c_0_25, plain, ![X58, X59]:k1_enumset1(X58,X58,X59)=k2_tarski(X58,X59), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 2.76/2.93  fof(c_0_26, negated_conjecture, ~(![X1, X2]:(r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)=>r2_hidden(X1,X2))), inference(assume_negation,[status(cth)],[t45_zfmisc_1])).
% 2.76/2.93  fof(c_0_27, plain, ![X42, X43, X44, X45, X46, X47, X48]:k5_enumset1(X42,X43,X44,X45,X46,X47,X48)=k2_xboole_0(k4_enumset1(X42,X43,X44,X45,X46,X47),k1_tarski(X48)), inference(variable_rename,[status(thm)],[t61_enumset1])).
% 2.76/2.93  fof(c_0_28, plain, ![X57]:k2_tarski(X57,X57)=k1_tarski(X57), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 2.76/2.93  cnf(c_0_29, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.76/2.93  cnf(c_0_30, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 2.76/2.93  fof(c_0_31, plain, ![X60, X61, X62]:k2_enumset1(X60,X60,X61,X62)=k1_enumset1(X60,X61,X62), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 2.76/2.93  fof(c_0_32, plain, ![X63, X64, X65, X66]:k3_enumset1(X63,X63,X64,X65,X66)=k2_enumset1(X63,X64,X65,X66), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 2.76/2.93  fof(c_0_33, plain, ![X67, X68, X69, X70, X71]:k4_enumset1(X67,X67,X68,X69,X70,X71)=k3_enumset1(X67,X68,X69,X70,X71), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 2.76/2.93  fof(c_0_34, plain, ![X72, X73, X74, X75, X76, X77]:k5_enumset1(X72,X72,X73,X74,X75,X76,X77)=k4_enumset1(X72,X73,X74,X75,X76,X77), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 2.76/2.93  fof(c_0_35, plain, ![X78, X79, X80, X81, X82, X83, X84]:k6_enumset1(X78,X78,X79,X80,X81,X82,X83,X84)=k5_enumset1(X78,X79,X80,X81,X82,X83,X84), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 2.76/2.93  fof(c_0_36, plain, ![X49, X50, X51, X52, X53, X54, X55, X56]:k6_enumset1(X49,X50,X51,X52,X53,X54,X55,X56)=k2_xboole_0(k4_enumset1(X49,X50,X51,X52,X53,X54),k2_tarski(X55,X56)), inference(variable_rename,[status(thm)],[t67_enumset1])).
% 2.76/2.93  fof(c_0_37, negated_conjecture, (r1_tarski(k2_xboole_0(k1_tarski(esk2_0),esk3_0),esk3_0)&~r2_hidden(esk2_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 2.76/2.93  fof(c_0_38, plain, ![X39, X40, X41]:k1_enumset1(X39,X40,X41)=k1_enumset1(X41,X40,X39), inference(variable_rename,[status(thm)],[t102_enumset1])).
% 2.76/2.93  cnf(c_0_39, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 2.76/2.93  cnf(c_0_40, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.76/2.93  cnf(c_0_41, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 2.76/2.93  cnf(c_0_42, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.76/2.93  cnf(c_0_43, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 2.76/2.93  cnf(c_0_44, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 2.76/2.93  cnf(c_0_45, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 2.76/2.93  cnf(c_0_46, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 2.76/2.93  cnf(c_0_47, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 2.76/2.93  fof(c_0_48, plain, ![X26, X27]:k3_xboole_0(X26,X27)=k5_xboole_0(k5_xboole_0(X26,X27),k2_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 2.76/2.93  fof(c_0_49, plain, ![X28, X29, X30, X31, X32, X33, X34, X35, X36, X37]:(((~r2_hidden(X32,X31)|(X32=X28|X32=X29|X32=X30)|X31!=k1_enumset1(X28,X29,X30))&(((X33!=X28|r2_hidden(X33,X31)|X31!=k1_enumset1(X28,X29,X30))&(X33!=X29|r2_hidden(X33,X31)|X31!=k1_enumset1(X28,X29,X30)))&(X33!=X30|r2_hidden(X33,X31)|X31!=k1_enumset1(X28,X29,X30))))&((((esk1_4(X34,X35,X36,X37)!=X34|~r2_hidden(esk1_4(X34,X35,X36,X37),X37)|X37=k1_enumset1(X34,X35,X36))&(esk1_4(X34,X35,X36,X37)!=X35|~r2_hidden(esk1_4(X34,X35,X36,X37),X37)|X37=k1_enumset1(X34,X35,X36)))&(esk1_4(X34,X35,X36,X37)!=X36|~r2_hidden(esk1_4(X34,X35,X36,X37),X37)|X37=k1_enumset1(X34,X35,X36)))&(r2_hidden(esk1_4(X34,X35,X36,X37),X37)|(esk1_4(X34,X35,X36,X37)=X34|esk1_4(X34,X35,X36,X37)=X35|esk1_4(X34,X35,X36,X37)=X36)|X37=k1_enumset1(X34,X35,X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 2.76/2.93  cnf(c_0_50, negated_conjecture, (r1_tarski(k2_xboole_0(k1_tarski(esk2_0),esk3_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 2.76/2.93  cnf(c_0_51, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 2.76/2.93  cnf(c_0_52, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40]), c_0_30]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46])).
% 2.76/2.93  cnf(c_0_53, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_30]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46])).
% 2.76/2.93  fof(c_0_54, plain, ![X12]:k3_xboole_0(X12,X12)=X12, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 2.76/2.93  cnf(c_0_55, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 2.76/2.93  fof(c_0_56, plain, ![X11]:k2_xboole_0(X11,X11)=X11, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 2.76/2.93  cnf(c_0_57, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 2.76/2.93  fof(c_0_58, plain, ![X18, X19]:r1_xboole_0(k3_xboole_0(X18,X19),k5_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[l97_xboole_1])).
% 2.76/2.93  fof(c_0_59, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 2.76/2.93  cnf(c_0_60, negated_conjecture, (r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)),esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_40]), c_0_30]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46])).
% 2.76/2.93  cnf(c_0_61, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_46])).
% 2.76/2.93  cnf(c_0_62, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X7)=k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[c_0_52, c_0_53])).
% 2.76/2.93  fof(c_0_63, plain, ![X20, X21]:r1_tarski(X20,k2_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 2.76/2.93  cnf(c_0_64, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_54])).
% 2.76/2.93  cnf(c_0_65, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_41]), c_0_42]), c_0_43])).
% 2.76/2.93  fof(c_0_66, plain, ![X25]:k5_xboole_0(X25,X25)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 2.76/2.93  cnf(c_0_67, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_56])).
% 2.76/2.93  fof(c_0_68, plain, ![X85, X86]:(~r1_xboole_0(k1_tarski(X85),X86)|~r2_hidden(X85,X86)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 2.76/2.93  fof(c_0_69, plain, ![X13, X14, X15]:(((~r2_hidden(X13,X14)|~r2_hidden(X13,X15)|~r2_hidden(X13,k5_xboole_0(X14,X15)))&(r2_hidden(X13,X14)|r2_hidden(X13,X15)|~r2_hidden(X13,k5_xboole_0(X14,X15))))&((~r2_hidden(X13,X14)|r2_hidden(X13,X15)|r2_hidden(X13,k5_xboole_0(X14,X15)))&(~r2_hidden(X13,X15)|r2_hidden(X13,X14)|r2_hidden(X13,k5_xboole_0(X14,X15))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 2.76/2.93  cnf(c_0_70, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 2.76/2.93  cnf(c_0_71, plain, (r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 2.76/2.93  fof(c_0_72, plain, ![X22, X23, X24]:k5_xboole_0(k5_xboole_0(X22,X23),X24)=k5_xboole_0(X22,k5_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 2.76/2.93  cnf(c_0_73, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 2.76/2.93  cnf(c_0_74, negated_conjecture, (r1_tarski(k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))),esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61]), c_0_62])).
% 2.76/2.93  cnf(c_0_75, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 2.76/2.93  cnf(c_0_76, plain, (k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65]), c_0_44]), c_0_45]), c_0_46])).
% 2.76/2.93  cnf(c_0_77, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_66])).
% 2.76/2.93  cnf(c_0_78, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 2.76/2.93  cnf(c_0_79, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 2.76/2.93  cnf(c_0_80, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X3,X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 2.76/2.93  cnf(c_0_81, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_70])])).
% 2.76/2.93  cnf(c_0_82, plain, (r1_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_65]), c_0_44]), c_0_45]), c_0_46])).
% 2.76/2.93  cnf(c_0_83, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 2.76/2.93  cnf(c_0_84, negated_conjecture, (k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))=esk3_0|~r1_tarski(esk3_0,k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 2.76/2.93  cnf(c_0_85, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 2.76/2.93  fof(c_0_86, plain, ![X9, X10]:k5_xboole_0(X9,X10)=k5_xboole_0(X10,X9), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 2.76/2.93  cnf(c_0_87, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77]), c_0_78])).
% 2.76/2.93  cnf(c_0_88, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_40]), c_0_30]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 2.76/2.93  cnf(c_0_89, plain, (r2_hidden(X1,k5_xboole_0(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X1)))|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 2.76/2.93  cnf(c_0_90, plain, (r1_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_82, c_0_83])).
% 2.76/2.93  cnf(c_0_91, negated_conjecture, (k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_85])])).
% 2.76/2.93  cnf(c_0_92, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 2.76/2.93  cnf(c_0_93, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_77]), c_0_87])).
% 2.76/2.93  cnf(c_0_94, plain, (r2_hidden(X1,X2)|~r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X1)))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 2.76/2.93  cnf(c_0_95, negated_conjecture, (r1_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(esk3_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_92]), c_0_93])).
% 2.76/2.93  cnf(c_0_96, negated_conjecture, (~r2_hidden(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 2.76/2.93  cnf(c_0_97, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_96]), ['proof']).
% 2.76/2.93  # SZS output end CNFRefutation
% 2.76/2.93  # Proof object total steps             : 98
% 2.76/2.93  # Proof object clause steps            : 49
% 2.76/2.93  # Proof object formula steps           : 49
% 2.76/2.93  # Proof object conjectures             : 11
% 2.76/2.93  # Proof object clause conjectures      : 8
% 2.76/2.93  # Proof object formula conjectures     : 3
% 2.76/2.93  # Proof object initial clauses used    : 25
% 2.76/2.93  # Proof object initial formulas used   : 24
% 2.76/2.93  # Proof object generating inferences   : 6
% 2.76/2.93  # Proof object simplifying inferences  : 136
% 2.76/2.93  # Training examples: 0 positive, 0 negative
% 2.76/2.93  # Parsed axioms                        : 24
% 2.76/2.93  # Removed by relevancy pruning/SinE    : 0
% 2.76/2.93  # Initial clauses                      : 37
% 2.76/2.93  # Removed in clause preprocessing      : 9
% 2.76/2.93  # Initial clauses in saturation        : 28
% 2.76/2.93  # Processed clauses                    : 4681
% 2.76/2.93  # ...of these trivial                  : 185
% 2.76/2.93  # ...subsumed                          : 3612
% 2.76/2.93  # ...remaining for further processing  : 884
% 2.76/2.93  # Other redundant clauses eliminated   : 161
% 2.76/2.93  # Clauses deleted for lack of memory   : 0
% 2.76/2.93  # Backward-subsumed                    : 23
% 2.76/2.93  # Backward-rewritten                   : 44
% 2.76/2.93  # Generated clauses                    : 131111
% 2.76/2.93  # ...of the previous two non-trivial   : 124354
% 2.76/2.93  # Contextual simplify-reflections      : 0
% 2.76/2.93  # Paramodulations                      : 130860
% 2.76/2.93  # Factorizations                       : 93
% 2.76/2.93  # Equation resolutions                 : 161
% 2.76/2.93  # Propositional unsat checks           : 0
% 2.76/2.93  #    Propositional check models        : 0
% 2.76/2.93  #    Propositional check unsatisfiable : 0
% 2.76/2.93  #    Propositional clauses             : 0
% 2.76/2.93  #    Propositional clauses after purity: 0
% 2.76/2.93  #    Propositional unsat core size     : 0
% 2.76/2.93  #    Propositional preprocessing time  : 0.000
% 2.76/2.93  #    Propositional encoding time       : 0.000
% 2.76/2.93  #    Propositional solver time         : 0.000
% 2.76/2.93  #    Success case prop preproc time    : 0.000
% 2.76/2.93  #    Success case prop encoding time   : 0.000
% 2.76/2.93  #    Success case prop solver time     : 0.000
% 2.76/2.93  # Current number of processed clauses  : 784
% 2.76/2.93  #    Positive orientable unit clauses  : 168
% 2.76/2.93  #    Positive unorientable unit clauses: 13
% 2.76/2.93  #    Negative unit clauses             : 99
% 2.76/2.93  #    Non-unit-clauses                  : 504
% 2.76/2.93  # Current number of unprocessed clauses: 119459
% 2.76/2.93  # ...number of literals in the above   : 630734
% 2.76/2.93  # Current number of archived formulas  : 0
% 2.76/2.93  # Current number of archived clauses   : 103
% 2.76/2.93  # Clause-clause subsumption calls (NU) : 64165
% 2.76/2.93  # Rec. Clause-clause subsumption calls : 36292
% 2.76/2.93  # Non-unit clause-clause subsumptions  : 1878
% 2.76/2.93  # Unit Clause-clause subsumption calls : 21944
% 2.76/2.93  # Rewrite failures with RHS unbound    : 0
% 2.76/2.93  # BW rewrite match attempts            : 14049
% 2.76/2.93  # BW rewrite match successes           : 887
% 2.76/2.93  # Condensation attempts                : 0
% 2.76/2.93  # Condensation successes               : 0
% 2.76/2.93  # Termbank termtop insertions          : 2999028
% 2.76/2.94  
% 2.76/2.94  # -------------------------------------------------
% 2.76/2.94  # User time                : 2.533 s
% 2.76/2.94  # System time              : 0.065 s
% 2.76/2.94  # Total time               : 2.599 s
% 2.76/2.94  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
