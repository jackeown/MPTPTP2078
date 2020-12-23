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
% DateTime   : Thu Dec  3 10:37:18 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  136 (8770 expanded)
%              Number of clauses        :   91 (3455 expanded)
%              Number of leaves         :   22 (2654 expanded)
%              Depth                    :   21
%              Number of atoms          :  264 (10345 expanded)
%              Number of equality atoms :  158 (9036 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t13_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(l75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(t56_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t62_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(c_0_22,plain,(
    ! [X19,X20,X21,X22,X23,X24,X25,X26] :
      ( ( r2_hidden(X22,X19)
        | ~ r2_hidden(X22,X21)
        | X21 != k4_xboole_0(X19,X20) )
      & ( ~ r2_hidden(X22,X20)
        | ~ r2_hidden(X22,X21)
        | X21 != k4_xboole_0(X19,X20) )
      & ( ~ r2_hidden(X23,X19)
        | r2_hidden(X23,X20)
        | r2_hidden(X23,X21)
        | X21 != k4_xboole_0(X19,X20) )
      & ( ~ r2_hidden(esk2_3(X24,X25,X26),X26)
        | ~ r2_hidden(esk2_3(X24,X25,X26),X24)
        | r2_hidden(esk2_3(X24,X25,X26),X25)
        | X26 = k4_xboole_0(X24,X25) )
      & ( r2_hidden(esk2_3(X24,X25,X26),X24)
        | r2_hidden(esk2_3(X24,X25,X26),X26)
        | X26 = k4_xboole_0(X24,X25) )
      & ( ~ r2_hidden(esk2_3(X24,X25,X26),X25)
        | r2_hidden(esk2_3(X24,X25,X26),X26)
        | X26 = k4_xboole_0(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_23,plain,(
    ! [X30,X31] : k4_xboole_0(X30,X31) = k5_xboole_0(X30,k3_xboole_0(X30,X31)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_24,plain,(
    ! [X39,X40,X41,X42,X43,X44,X45,X46,X47,X48] :
      ( ( ~ r2_hidden(X43,X42)
        | X43 = X39
        | X43 = X40
        | X43 = X41
        | X42 != k1_enumset1(X39,X40,X41) )
      & ( X44 != X39
        | r2_hidden(X44,X42)
        | X42 != k1_enumset1(X39,X40,X41) )
      & ( X44 != X40
        | r2_hidden(X44,X42)
        | X42 != k1_enumset1(X39,X40,X41) )
      & ( X44 != X41
        | r2_hidden(X44,X42)
        | X42 != k1_enumset1(X39,X40,X41) )
      & ( esk3_4(X45,X46,X47,X48) != X45
        | ~ r2_hidden(esk3_4(X45,X46,X47,X48),X48)
        | X48 = k1_enumset1(X45,X46,X47) )
      & ( esk3_4(X45,X46,X47,X48) != X46
        | ~ r2_hidden(esk3_4(X45,X46,X47,X48),X48)
        | X48 = k1_enumset1(X45,X46,X47) )
      & ( esk3_4(X45,X46,X47,X48) != X47
        | ~ r2_hidden(esk3_4(X45,X46,X47,X48),X48)
        | X48 = k1_enumset1(X45,X46,X47) )
      & ( r2_hidden(esk3_4(X45,X46,X47,X48),X48)
        | esk3_4(X45,X46,X47,X48) = X45
        | esk3_4(X45,X46,X47,X48) = X46
        | esk3_4(X45,X46,X47,X48) = X47
        | X48 = k1_enumset1(X45,X46,X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_25,plain,(
    ! [X87,X88,X89] : k2_enumset1(X87,X87,X88,X89) = k1_enumset1(X87,X88,X89) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X90,X91,X92,X93] : k3_enumset1(X90,X90,X91,X92,X93) = k2_enumset1(X90,X91,X92,X93) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_27,plain,(
    ! [X35,X36] : r1_tarski(X35,k2_xboole_0(X35,X36)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_28,plain,(
    ! [X37,X38] : k2_xboole_0(X37,X38) = k5_xboole_0(X37,k4_xboole_0(X38,X37)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_29,plain,(
    ! [X32] : k2_xboole_0(X32,k1_xboole_0) = X32 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_30,plain,(
    ! [X9,X10] : k2_xboole_0(X9,X10) = k2_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_36,plain,(
    ! [X33,X34] :
      ( ~ r1_tarski(X33,X34)
      | k3_xboole_0(X33,X34) = X33 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_32])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_38]),c_0_32])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_38]),c_0_38]),c_0_32]),c_0_32])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_42])])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = X1 ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) = X1 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k3_enumset1(X3,X3,X3,X4,X1)))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

fof(c_0_53,plain,(
    ! [X13,X14,X15,X16,X17] :
      ( ( ~ r1_tarski(X13,X14)
        | ~ r2_hidden(X15,X13)
        | r2_hidden(X15,X14) )
      & ( r2_hidden(esk1_2(X16,X17),X16)
        | r1_tarski(X16,X17) )
      & ( ~ r2_hidden(esk1_2(X16,X17),X17)
        | r1_tarski(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_54,plain,(
    ! [X11,X12] : k3_xboole_0(X11,X12) = k3_xboole_0(X12,X11) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_57,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t13_zfmisc_1])).

fof(c_0_58,plain,(
    ! [X57,X58,X59,X60] : k2_enumset1(X57,X58,X59,X60) = k2_xboole_0(k2_tarski(X57,X58),k2_tarski(X59,X60)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

fof(c_0_59,plain,(
    ! [X85,X86] : k1_enumset1(X85,X85,X86) = k2_tarski(X85,X86) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_60,plain,(
    ! [X61,X62,X63,X64,X65,X66,X67,X68] : k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68) = k2_xboole_0(k2_enumset1(X61,X62,X63,X64),k2_enumset1(X65,X66,X67,X68)) ),
    inference(variable_rename,[status(thm)],[l75_enumset1])).

fof(c_0_61,plain,(
    ! [X69,X70,X71,X72,X73,X74,X75] : k5_enumset1(X69,X70,X71,X72,X73,X74,X75) = k2_xboole_0(k1_tarski(X69),k4_enumset1(X70,X71,X72,X73,X74,X75)) ),
    inference(variable_rename,[status(thm)],[t56_enumset1])).

fof(c_0_62,plain,(
    ! [X84] : k2_tarski(X84,X84) = k1_tarski(X84) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_63,plain,(
    ! [X94,X95,X96,X97,X98,X99] : k5_enumset1(X94,X94,X95,X96,X97,X98,X99) = k4_enumset1(X94,X95,X96,X97,X98,X99) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_64,plain,(
    ! [X76,X77,X78,X79,X80,X81,X82,X83] : k6_enumset1(X76,X77,X78,X79,X80,X81,X82,X83) = k2_xboole_0(k1_tarski(X76),k5_enumset1(X77,X78,X79,X80,X81,X82,X83)) ),
    inference(variable_rename,[status(thm)],[t62_enumset1])).

cnf(c_0_65,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_66,plain,
    ( r1_tarski(k5_xboole_0(k1_xboole_0,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

fof(c_0_67,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)) = k1_tarski(esk5_0)
    & esk5_0 != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_57])])])).

cnf(c_0_68,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_69,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_70,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_71,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_72,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_73,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_74,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_75,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_52])).

cnf(c_0_76,plain,
    ( k3_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X1) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_66])).

fof(c_0_77,plain,(
    ! [X28,X29] :
      ( ( r1_tarski(X28,X29)
        | X28 != X29 )
      & ( r1_tarski(X29,X28)
        | X28 != X29 )
      & ( ~ r1_tarski(X28,X29)
        | ~ r1_tarski(X29,X28)
        | X28 = X29 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_78,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)) = k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_79,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X1,X1,X1,X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69]),c_0_69]),c_0_38]),c_0_32]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_80,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k5_xboole_0(k3_enumset1(X5,X5,X6,X7,X8),k3_xboole_0(k3_enumset1(X5,X5,X6,X7,X8),k3_enumset1(X1,X1,X2,X3,X4)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_38]),c_0_32]),c_0_35]),c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_81,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k5_xboole_0(k5_enumset1(X2,X2,X3,X4,X5,X6,X7),k3_xboole_0(k5_enumset1(X2,X2,X3,X4,X5,X6,X7),k3_enumset1(X1,X1,X1,X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_72]),c_0_69]),c_0_38]),c_0_32]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_73]),c_0_73])).

cnf(c_0_82,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k5_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k3_enumset1(X1,X1,X1,X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_72]),c_0_69]),c_0_38]),c_0_32]),c_0_34]),c_0_34]),c_0_35]),c_0_35])).

cnf(c_0_83,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_84,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_85,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_86,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))) = k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_72]),c_0_72]),c_0_72]),c_0_69]),c_0_69]),c_0_69]),c_0_38]),c_0_32]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_87,plain,
    ( k6_enumset1(X1,X1,X1,X2,X3,X3,X3,X4) = k3_enumset1(X1,X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_88,plain,
    ( k6_enumset1(X1,X2,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_89,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_83,c_0_32])).

cnf(c_0_90,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_55,c_0_84])).

cnf(c_0_91,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_85])).

cnf(c_0_92,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = X1 ),
    inference(spm,[status(thm)],[c_0_49,c_0_46])).

cnf(c_0_93,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))) = k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_86,c_0_65])).

cnf(c_0_94,plain,
    ( k5_enumset1(X1,X1,X2,X3,X3,X3,X4) = k3_enumset1(X1,X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_95,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_96,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | r2_hidden(esk2_3(X1,X2,k1_xboole_0),X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_89]),c_0_52]),c_0_52]),c_0_52]),c_0_90])).

cnf(c_0_97,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_43,c_0_91])).

cnf(c_0_98,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_99,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) = X1 ),
    inference(spm,[status(thm)],[c_0_92,c_0_65])).

cnf(c_0_100,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_xboole_0(k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))) = k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_94]),c_0_94]),c_0_94]),c_0_94]),c_0_94])).

cnf(c_0_101,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_95,c_0_32])).

cnf(c_0_102,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0
    | r2_hidden(esk2_3(X1,X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_103,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_45,c_0_52])).

cnf(c_0_104,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_34]),c_0_35])).

cnf(c_0_105,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_65])).

cnf(c_0_106,negated_conjecture,
    ( k3_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) = k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_65])).

cnf(c_0_107,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_97])]),c_0_90])).

cnf(c_0_108,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_103,c_0_84])).

cnf(c_0_109,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_104])])).

cnf(c_0_110,plain,
    ( k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)))) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(spm,[status(thm)],[c_0_82,c_0_94])).

cnf(c_0_111,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k5_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) = k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_107]),c_0_108])).

cnf(c_0_112,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k3_enumset1(X1,X1,X1,X3,X4)))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_109])).

cnf(c_0_113,negated_conjecture,
    ( k5_enumset1(esk6_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_106]),c_0_111]),c_0_88])).

cnf(c_0_114,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_115,plain,(
    ! [X50,X51,X52,X53,X54,X55] :
      ( ( ~ r2_hidden(X52,X51)
        | X52 = X50
        | X51 != k1_tarski(X50) )
      & ( X53 != X50
        | r2_hidden(X53,X51)
        | X51 != k1_tarski(X50) )
      & ( ~ r2_hidden(esk4_2(X54,X55),X55)
        | esk4_2(X54,X55) != X54
        | X55 = k1_tarski(X54) )
      & ( r2_hidden(esk4_2(X54,X55),X55)
        | esk4_2(X54,X55) = X54
        | X55 = k1_tarski(X54) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_116,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k5_enumset1(X1,X1,X1,X3,X3,X3,X4)))) ),
    inference(spm,[status(thm)],[c_0_112,c_0_94])).

cnf(c_0_117,plain,
    ( k5_enumset1(X1,X1,X1,X2,X3,X4,X5) = k5_enumset1(X1,X2,X3,X4,X4,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_94]),c_0_80]),c_0_88]),c_0_88])).

cnf(c_0_118,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k6_enumset1(X5,X6,X7,X8,X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_46]),c_0_80])).

cnf(c_0_119,negated_conjecture,
    ( k6_enumset1(X1,esk6_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k5_enumset1(X1,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_113]),c_0_82]),c_0_88])).

cnf(c_0_120,plain,
    ( r2_hidden(X1,X4)
    | r2_hidden(X1,X3)
    | X4 != k5_xboole_0(X2,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_114,c_0_32])).

cnf(c_0_121,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_115])).

cnf(c_0_122,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k5_enumset1(X1,X3,X3,X3,X3,X3,X4)))) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_123,negated_conjecture,
    ( k5_enumset1(X1,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k5_enumset1(esk5_0,esk5_0,esk5_0,X1,esk6_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_88])).

cnf(c_0_124,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_120])).

cnf(c_0_125,plain,
    ( X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_121,c_0_72]),c_0_69]),c_0_34]),c_0_35])).

cnf(c_0_126,negated_conjecture,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k5_enumset1(esk5_0,esk5_0,esk5_0,X1,esk6_0,esk5_0,esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_122,c_0_123])).

cnf(c_0_127,plain,
    ( r2_hidden(X1,k5_xboole_0(k3_enumset1(X2,X2,X2,X3,X1),k3_xboole_0(k3_enumset1(X2,X2,X2,X3,X1),X4)))
    | r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_124,c_0_48])).

cnf(c_0_128,negated_conjecture,
    ( k5_enumset1(esk5_0,esk5_0,esk5_0,esk6_0,esk6_0,esk5_0,esk5_0) = k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_113,c_0_123])).

cnf(c_0_129,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_125])).

cnf(c_0_130,negated_conjecture,
    ( r2_hidden(X1,k5_enumset1(esk5_0,esk5_0,esk5_0,X1,esk6_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_131,negated_conjecture,
    ( k5_enumset1(X1,esk5_0,esk5_0,esk6_0,esk6_0,esk5_0,esk5_0) = k5_enumset1(X1,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_128]),c_0_82]),c_0_88]),c_0_88])).

cnf(c_0_132,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_129,c_0_94])).

cnf(c_0_133,negated_conjecture,
    ( r2_hidden(esk6_0,k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_130,c_0_131])).

cnf(c_0_134,negated_conjecture,
    ( esk5_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_135,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_133]),c_0_134]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:48:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.51  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.19/0.51  # and selection function GSelectMinInfpos.
% 0.19/0.51  #
% 0.19/0.51  # Preprocessing time       : 0.029 s
% 0.19/0.51  # Presaturation interreduction done
% 0.19/0.51  
% 0.19/0.51  # Proof found!
% 0.19/0.51  # SZS status Theorem
% 0.19/0.51  # SZS output start CNFRefutation
% 0.19/0.51  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.19/0.51  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.51  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.19/0.51  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.51  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.51  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.51  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.19/0.51  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.19/0.51  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.19/0.51  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.51  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.51  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.51  fof(t13_zfmisc_1, conjecture, ![X1, X2]:(k2_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 0.19/0.51  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 0.19/0.51  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.51  fof(l75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l75_enumset1)).
% 0.19/0.51  fof(t56_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_enumset1)).
% 0.19/0.51  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.51  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.51  fof(t62_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_enumset1)).
% 0.19/0.51  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.51  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.51  fof(c_0_22, plain, ![X19, X20, X21, X22, X23, X24, X25, X26]:((((r2_hidden(X22,X19)|~r2_hidden(X22,X21)|X21!=k4_xboole_0(X19,X20))&(~r2_hidden(X22,X20)|~r2_hidden(X22,X21)|X21!=k4_xboole_0(X19,X20)))&(~r2_hidden(X23,X19)|r2_hidden(X23,X20)|r2_hidden(X23,X21)|X21!=k4_xboole_0(X19,X20)))&((~r2_hidden(esk2_3(X24,X25,X26),X26)|(~r2_hidden(esk2_3(X24,X25,X26),X24)|r2_hidden(esk2_3(X24,X25,X26),X25))|X26=k4_xboole_0(X24,X25))&((r2_hidden(esk2_3(X24,X25,X26),X24)|r2_hidden(esk2_3(X24,X25,X26),X26)|X26=k4_xboole_0(X24,X25))&(~r2_hidden(esk2_3(X24,X25,X26),X25)|r2_hidden(esk2_3(X24,X25,X26),X26)|X26=k4_xboole_0(X24,X25))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.19/0.51  fof(c_0_23, plain, ![X30, X31]:k4_xboole_0(X30,X31)=k5_xboole_0(X30,k3_xboole_0(X30,X31)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.51  fof(c_0_24, plain, ![X39, X40, X41, X42, X43, X44, X45, X46, X47, X48]:(((~r2_hidden(X43,X42)|(X43=X39|X43=X40|X43=X41)|X42!=k1_enumset1(X39,X40,X41))&(((X44!=X39|r2_hidden(X44,X42)|X42!=k1_enumset1(X39,X40,X41))&(X44!=X40|r2_hidden(X44,X42)|X42!=k1_enumset1(X39,X40,X41)))&(X44!=X41|r2_hidden(X44,X42)|X42!=k1_enumset1(X39,X40,X41))))&((((esk3_4(X45,X46,X47,X48)!=X45|~r2_hidden(esk3_4(X45,X46,X47,X48),X48)|X48=k1_enumset1(X45,X46,X47))&(esk3_4(X45,X46,X47,X48)!=X46|~r2_hidden(esk3_4(X45,X46,X47,X48),X48)|X48=k1_enumset1(X45,X46,X47)))&(esk3_4(X45,X46,X47,X48)!=X47|~r2_hidden(esk3_4(X45,X46,X47,X48),X48)|X48=k1_enumset1(X45,X46,X47)))&(r2_hidden(esk3_4(X45,X46,X47,X48),X48)|(esk3_4(X45,X46,X47,X48)=X45|esk3_4(X45,X46,X47,X48)=X46|esk3_4(X45,X46,X47,X48)=X47)|X48=k1_enumset1(X45,X46,X47)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.19/0.51  fof(c_0_25, plain, ![X87, X88, X89]:k2_enumset1(X87,X87,X88,X89)=k1_enumset1(X87,X88,X89), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.51  fof(c_0_26, plain, ![X90, X91, X92, X93]:k3_enumset1(X90,X90,X91,X92,X93)=k2_enumset1(X90,X91,X92,X93), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.51  fof(c_0_27, plain, ![X35, X36]:r1_tarski(X35,k2_xboole_0(X35,X36)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.51  fof(c_0_28, plain, ![X37, X38]:k2_xboole_0(X37,X38)=k5_xboole_0(X37,k4_xboole_0(X38,X37)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.19/0.51  fof(c_0_29, plain, ![X32]:k2_xboole_0(X32,k1_xboole_0)=X32, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.19/0.51  fof(c_0_30, plain, ![X9, X10]:k2_xboole_0(X9,X10)=k2_xboole_0(X10,X9), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.19/0.51  cnf(c_0_31, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.51  cnf(c_0_32, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.51  cnf(c_0_33, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.51  cnf(c_0_34, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.51  cnf(c_0_35, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.51  fof(c_0_36, plain, ![X33, X34]:(~r1_tarski(X33,X34)|k3_xboole_0(X33,X34)=X33), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.51  cnf(c_0_37, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.51  cnf(c_0_38, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.51  cnf(c_0_39, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.51  cnf(c_0_40, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.51  cnf(c_0_41, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.51  cnf(c_0_42, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.19/0.51  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.51  cnf(c_0_44, plain, (r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38]), c_0_32])).
% 0.19/0.51  cnf(c_0_45, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_38]), c_0_32])).
% 0.19/0.51  cnf(c_0_46, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_38]), c_0_38]), c_0_32]), c_0_32])).
% 0.19/0.51  cnf(c_0_47, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_41])).
% 0.19/0.51  cnf(c_0_48, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_42])])).
% 0.19/0.51  cnf(c_0_49, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=X1), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.51  cnf(c_0_50, plain, (k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)))=X1), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.51  cnf(c_0_51, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k3_enumset1(X3,X3,X3,X4,X1))))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.51  cnf(c_0_52, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.51  fof(c_0_53, plain, ![X13, X14, X15, X16, X17]:((~r1_tarski(X13,X14)|(~r2_hidden(X15,X13)|r2_hidden(X15,X14)))&((r2_hidden(esk1_2(X16,X17),X16)|r1_tarski(X16,X17))&(~r2_hidden(esk1_2(X16,X17),X17)|r1_tarski(X16,X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.51  fof(c_0_54, plain, ![X11, X12]:k3_xboole_0(X11,X12)=k3_xboole_0(X12,X11), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.51  cnf(c_0_55, plain, (~r2_hidden(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.51  cnf(c_0_56, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.51  fof(c_0_57, negated_conjecture, ~(![X1, X2]:(k2_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2)), inference(assume_negation,[status(cth)],[t13_zfmisc_1])).
% 0.19/0.51  fof(c_0_58, plain, ![X57, X58, X59, X60]:k2_enumset1(X57,X58,X59,X60)=k2_xboole_0(k2_tarski(X57,X58),k2_tarski(X59,X60)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 0.19/0.51  fof(c_0_59, plain, ![X85, X86]:k1_enumset1(X85,X85,X86)=k2_tarski(X85,X86), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.51  fof(c_0_60, plain, ![X61, X62, X63, X64, X65, X66, X67, X68]:k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68)=k2_xboole_0(k2_enumset1(X61,X62,X63,X64),k2_enumset1(X65,X66,X67,X68)), inference(variable_rename,[status(thm)],[l75_enumset1])).
% 0.19/0.51  fof(c_0_61, plain, ![X69, X70, X71, X72, X73, X74, X75]:k5_enumset1(X69,X70,X71,X72,X73,X74,X75)=k2_xboole_0(k1_tarski(X69),k4_enumset1(X70,X71,X72,X73,X74,X75)), inference(variable_rename,[status(thm)],[t56_enumset1])).
% 0.19/0.51  fof(c_0_62, plain, ![X84]:k2_tarski(X84,X84)=k1_tarski(X84), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.51  fof(c_0_63, plain, ![X94, X95, X96, X97, X98, X99]:k5_enumset1(X94,X94,X95,X96,X97,X98,X99)=k4_enumset1(X94,X95,X96,X97,X98,X99), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.51  fof(c_0_64, plain, ![X76, X77, X78, X79, X80, X81, X82, X83]:k6_enumset1(X76,X77,X78,X79,X80,X81,X82,X83)=k2_xboole_0(k1_tarski(X76),k5_enumset1(X77,X78,X79,X80,X81,X82,X83)), inference(variable_rename,[status(thm)],[t62_enumset1])).
% 0.19/0.51  cnf(c_0_65, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.51  cnf(c_0_66, plain, (r1_tarski(k5_xboole_0(k1_xboole_0,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.51  fof(c_0_67, negated_conjecture, (k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))=k1_tarski(esk5_0)&esk5_0!=esk6_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_57])])])).
% 0.19/0.51  cnf(c_0_68, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.51  cnf(c_0_69, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.51  cnf(c_0_70, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.51  cnf(c_0_71, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.51  cnf(c_0_72, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.51  cnf(c_0_73, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.51  cnf(c_0_74, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.51  cnf(c_0_75, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_65, c_0_52])).
% 0.19/0.51  cnf(c_0_76, plain, (k3_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X1)=k5_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_43, c_0_66])).
% 0.19/0.51  fof(c_0_77, plain, ![X28, X29]:(((r1_tarski(X28,X29)|X28!=X29)&(r1_tarski(X29,X28)|X28!=X29))&(~r1_tarski(X28,X29)|~r1_tarski(X29,X28)|X28=X29)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.51  cnf(c_0_78, negated_conjecture, (k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.51  cnf(c_0_79, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X1,X1,X1,X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_69]), c_0_69]), c_0_38]), c_0_32]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_35])).
% 0.19/0.51  cnf(c_0_80, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k5_xboole_0(k3_enumset1(X5,X5,X6,X7,X8),k3_xboole_0(k3_enumset1(X5,X5,X6,X7,X8),k3_enumset1(X1,X1,X2,X3,X4))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_38]), c_0_32]), c_0_35]), c_0_35]), c_0_35]), c_0_35])).
% 0.19/0.51  cnf(c_0_81, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k5_xboole_0(k5_enumset1(X2,X2,X3,X4,X5,X6,X7),k3_xboole_0(k5_enumset1(X2,X2,X3,X4,X5,X6,X7),k3_enumset1(X1,X1,X1,X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_72]), c_0_69]), c_0_38]), c_0_32]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_73]), c_0_73])).
% 0.19/0.51  cnf(c_0_82, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k5_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k3_enumset1(X1,X1,X1,X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_72]), c_0_69]), c_0_38]), c_0_32]), c_0_34]), c_0_34]), c_0_35]), c_0_35])).
% 0.19/0.51  cnf(c_0_83, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.51  cnf(c_0_84, plain, (k5_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.19/0.51  cnf(c_0_85, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.19/0.51  cnf(c_0_86, negated_conjecture, (k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))))=k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_72]), c_0_72]), c_0_72]), c_0_69]), c_0_69]), c_0_69]), c_0_38]), c_0_32]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_35])).
% 0.19/0.51  cnf(c_0_87, plain, (k6_enumset1(X1,X1,X1,X2,X3,X3,X3,X4)=k3_enumset1(X1,X1,X2,X3,X4)), inference(rw,[status(thm)],[c_0_79, c_0_80])).
% 0.19/0.51  cnf(c_0_88, plain, (k6_enumset1(X1,X2,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[c_0_81, c_0_82])).
% 0.19/0.51  cnf(c_0_89, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_83, c_0_32])).
% 0.19/0.51  cnf(c_0_90, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_55, c_0_84])).
% 0.19/0.51  cnf(c_0_91, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_85])).
% 0.19/0.51  cnf(c_0_92, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=X1), inference(spm,[status(thm)],[c_0_49, c_0_46])).
% 0.19/0.51  cnf(c_0_93, negated_conjecture, (k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))))=k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[c_0_86, c_0_65])).
% 0.19/0.51  cnf(c_0_94, plain, (k5_enumset1(X1,X1,X2,X3,X3,X3,X4)=k3_enumset1(X1,X1,X2,X3,X4)), inference(rw,[status(thm)],[c_0_87, c_0_88])).
% 0.19/0.51  cnf(c_0_95, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.51  cnf(c_0_96, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|r2_hidden(esk2_3(X1,X2,k1_xboole_0),X1)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_89]), c_0_52]), c_0_52]), c_0_52]), c_0_90])).
% 0.19/0.51  cnf(c_0_97, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_43, c_0_91])).
% 0.19/0.51  cnf(c_0_98, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.51  cnf(c_0_99, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1))))=X1), inference(spm,[status(thm)],[c_0_92, c_0_65])).
% 0.19/0.51  cnf(c_0_100, negated_conjecture, (k5_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_xboole_0(k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))))=k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_94]), c_0_94]), c_0_94]), c_0_94]), c_0_94])).
% 0.19/0.51  cnf(c_0_101, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_95, c_0_32])).
% 0.19/0.51  cnf(c_0_102, plain, (k5_xboole_0(X1,X1)=k1_xboole_0|r2_hidden(esk2_3(X1,X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.19/0.51  cnf(c_0_103, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_45, c_0_52])).
% 0.19/0.51  cnf(c_0_104, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X2,X2,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98, c_0_34]), c_0_35])).
% 0.19/0.51  cnf(c_0_105, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_46, c_0_65])).
% 0.19/0.51  cnf(c_0_106, negated_conjecture, (k3_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))=k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_65])).
% 0.19/0.51  cnf(c_0_107, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_97])]), c_0_90])).
% 0.19/0.51  cnf(c_0_108, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_103, c_0_84])).
% 0.19/0.51  cnf(c_0_109, plain, (r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_104])])).
% 0.19/0.51  cnf(c_0_110, plain, (k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))))=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(spm,[status(thm)],[c_0_82, c_0_94])).
% 0.19/0.51  cnf(c_0_111, negated_conjecture, (k5_xboole_0(k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k5_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))=k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_107]), c_0_108])).
% 0.19/0.51  cnf(c_0_112, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k3_enumset1(X1,X1,X1,X3,X4))))), inference(spm,[status(thm)],[c_0_47, c_0_109])).
% 0.19/0.51  cnf(c_0_113, negated_conjecture, (k5_enumset1(esk6_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_106]), c_0_111]), c_0_88])).
% 0.19/0.51  cnf(c_0_114, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.51  fof(c_0_115, plain, ![X50, X51, X52, X53, X54, X55]:(((~r2_hidden(X52,X51)|X52=X50|X51!=k1_tarski(X50))&(X53!=X50|r2_hidden(X53,X51)|X51!=k1_tarski(X50)))&((~r2_hidden(esk4_2(X54,X55),X55)|esk4_2(X54,X55)!=X54|X55=k1_tarski(X54))&(r2_hidden(esk4_2(X54,X55),X55)|esk4_2(X54,X55)=X54|X55=k1_tarski(X54)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.51  cnf(c_0_116, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k5_enumset1(X1,X1,X1,X3,X3,X3,X4))))), inference(spm,[status(thm)],[c_0_112, c_0_94])).
% 0.19/0.51  cnf(c_0_117, plain, (k5_enumset1(X1,X1,X1,X2,X3,X4,X5)=k5_enumset1(X1,X2,X3,X4,X4,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_94]), c_0_80]), c_0_88]), c_0_88])).
% 0.19/0.51  cnf(c_0_118, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k6_enumset1(X5,X6,X7,X8,X1,X2,X3,X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_46]), c_0_80])).
% 0.19/0.51  cnf(c_0_119, negated_conjecture, (k6_enumset1(X1,esk6_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k5_enumset1(X1,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_113]), c_0_82]), c_0_88])).
% 0.19/0.51  cnf(c_0_120, plain, (r2_hidden(X1,X4)|r2_hidden(X1,X3)|X4!=k5_xboole_0(X2,k3_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_114, c_0_32])).
% 0.19/0.51  cnf(c_0_121, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_115])).
% 0.19/0.51  cnf(c_0_122, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k5_enumset1(X1,X3,X3,X3,X3,X3,X4))))), inference(spm,[status(thm)],[c_0_116, c_0_117])).
% 0.19/0.51  cnf(c_0_123, negated_conjecture, (k5_enumset1(X1,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k5_enumset1(esk5_0,esk5_0,esk5_0,X1,esk6_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_88])).
% 0.19/0.51  cnf(c_0_124, plain, (r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_120])).
% 0.19/0.51  cnf(c_0_125, plain, (X1=X3|X2!=k3_enumset1(X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_121, c_0_72]), c_0_69]), c_0_34]), c_0_35])).
% 0.19/0.51  cnf(c_0_126, negated_conjecture, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k5_enumset1(esk5_0,esk5_0,esk5_0,X1,esk6_0,esk5_0,esk5_0))))), inference(spm,[status(thm)],[c_0_122, c_0_123])).
% 0.19/0.51  cnf(c_0_127, plain, (r2_hidden(X1,k5_xboole_0(k3_enumset1(X2,X2,X2,X3,X1),k3_xboole_0(k3_enumset1(X2,X2,X2,X3,X1),X4)))|r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_124, c_0_48])).
% 0.19/0.51  cnf(c_0_128, negated_conjecture, (k5_enumset1(esk5_0,esk5_0,esk5_0,esk6_0,esk6_0,esk5_0,esk5_0)=k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[c_0_113, c_0_123])).
% 0.19/0.51  cnf(c_0_129, plain, (X1=X2|~r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_125])).
% 0.19/0.51  cnf(c_0_130, negated_conjecture, (r2_hidden(X1,k5_enumset1(esk5_0,esk5_0,esk5_0,X1,esk6_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_126, c_0_127])).
% 0.19/0.51  cnf(c_0_131, negated_conjecture, (k5_enumset1(X1,esk5_0,esk5_0,esk6_0,esk6_0,esk5_0,esk5_0)=k5_enumset1(X1,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_128]), c_0_82]), c_0_88]), c_0_88])).
% 0.19/0.51  cnf(c_0_132, plain, (X1=X2|~r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))), inference(spm,[status(thm)],[c_0_129, c_0_94])).
% 0.19/0.51  cnf(c_0_133, negated_conjecture, (r2_hidden(esk6_0,k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_130, c_0_131])).
% 0.19/0.51  cnf(c_0_134, negated_conjecture, (esk5_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.51  cnf(c_0_135, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_133]), c_0_134]), ['proof']).
% 0.19/0.51  # SZS output end CNFRefutation
% 0.19/0.51  # Proof object total steps             : 136
% 0.19/0.51  # Proof object clause steps            : 91
% 0.19/0.51  # Proof object formula steps           : 45
% 0.19/0.51  # Proof object conjectures             : 19
% 0.19/0.51  # Proof object clause conjectures      : 16
% 0.19/0.51  # Proof object formula conjectures     : 3
% 0.19/0.51  # Proof object initial clauses used    : 27
% 0.19/0.51  # Proof object initial formulas used   : 22
% 0.19/0.51  # Proof object generating inferences   : 34
% 0.19/0.51  # Proof object simplifying inferences  : 119
% 0.19/0.51  # Training examples: 0 positive, 0 negative
% 0.19/0.51  # Parsed axioms                        : 22
% 0.19/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.51  # Initial clauses                      : 42
% 0.19/0.51  # Removed in clause preprocessing      : 7
% 0.19/0.51  # Initial clauses in saturation        : 35
% 0.19/0.51  # Processed clauses                    : 1145
% 0.19/0.51  # ...of these trivial                  : 85
% 0.19/0.51  # ...subsumed                          : 715
% 0.19/0.51  # ...remaining for further processing  : 345
% 0.19/0.51  # Other redundant clauses eliminated   : 27
% 0.19/0.51  # Clauses deleted for lack of memory   : 0
% 0.19/0.51  # Backward-subsumed                    : 1
% 0.19/0.51  # Backward-rewritten                   : 65
% 0.19/0.51  # Generated clauses                    : 6756
% 0.19/0.51  # ...of the previous two non-trivial   : 5569
% 0.19/0.51  # Contextual simplify-reflections      : 0
% 0.19/0.51  # Paramodulations                      : 6731
% 0.19/0.51  # Factorizations                       : 2
% 0.19/0.51  # Equation resolutions                 : 27
% 0.19/0.51  # Propositional unsat checks           : 0
% 0.19/0.51  #    Propositional check models        : 0
% 0.19/0.51  #    Propositional check unsatisfiable : 0
% 0.19/0.51  #    Propositional clauses             : 0
% 0.19/0.51  #    Propositional clauses after purity: 0
% 0.19/0.51  #    Propositional unsat core size     : 0
% 0.19/0.51  #    Propositional preprocessing time  : 0.000
% 0.19/0.51  #    Propositional encoding time       : 0.000
% 0.19/0.51  #    Propositional solver time         : 0.000
% 0.19/0.51  #    Success case prop preproc time    : 0.000
% 0.19/0.51  #    Success case prop encoding time   : 0.000
% 0.19/0.51  #    Success case prop solver time     : 0.000
% 0.19/0.51  # Current number of processed clauses  : 235
% 0.19/0.51  #    Positive orientable unit clauses  : 69
% 0.19/0.51  #    Positive unorientable unit clauses: 7
% 0.19/0.51  #    Negative unit clauses             : 73
% 0.19/0.51  #    Non-unit-clauses                  : 86
% 0.19/0.51  # Current number of unprocessed clauses: 4427
% 0.19/0.51  # ...number of literals in the above   : 11844
% 0.19/0.51  # Current number of archived formulas  : 0
% 0.19/0.51  # Current number of archived clauses   : 106
% 0.19/0.51  # Clause-clause subsumption calls (NU) : 1192
% 0.19/0.51  # Rec. Clause-clause subsumption calls : 1051
% 0.19/0.51  # Non-unit clause-clause subsumptions  : 188
% 0.19/0.51  # Unit Clause-clause subsumption calls : 1331
% 0.19/0.51  # Rewrite failures with RHS unbound    : 0
% 0.19/0.51  # BW rewrite match attempts            : 457
% 0.19/0.51  # BW rewrite match successes           : 114
% 0.19/0.51  # Condensation attempts                : 0
% 0.19/0.51  # Condensation successes               : 0
% 0.19/0.51  # Termbank termtop insertions          : 99087
% 0.19/0.51  
% 0.19/0.51  # -------------------------------------------------
% 0.19/0.51  # User time                : 0.165 s
% 0.19/0.51  # System time              : 0.011 s
% 0.19/0.51  # Total time               : 0.176 s
% 0.19/0.51  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
