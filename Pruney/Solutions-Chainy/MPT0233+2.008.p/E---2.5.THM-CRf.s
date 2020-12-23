%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:38:58 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  102 (1795 expanded)
%              Number of clauses        :   55 ( 667 expanded)
%              Number of leaves         :   23 ( 560 expanded)
%              Depth                    :   14
%              Number of atoms          :  185 (1996 expanded)
%              Number of equality atoms :  132 (1771 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))
        & X1 != X3
        & X1 != X4 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

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

fof(t18_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k3_xboole_0(X2,X3))
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t12_zfmisc_1,axiom,(
    ! [X1,X2] : r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(t98_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X1,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))
          & X1 != X3
          & X1 != X4 ) ),
    inference(assume_negation,[status(cth)],[t28_zfmisc_1])).

fof(c_0_24,negated_conjecture,
    ( r1_tarski(k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0))
    & esk3_0 != esk5_0
    & esk3_0 != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

fof(c_0_25,plain,(
    ! [X54,X55] : k1_enumset1(X54,X54,X55) = k2_tarski(X54,X55) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_26,plain,(
    ! [X56,X57,X58] : k2_enumset1(X56,X56,X57,X58) = k1_enumset1(X56,X57,X58) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_27,plain,(
    ! [X59,X60,X61,X62] : k3_enumset1(X59,X59,X60,X61,X62) = k2_enumset1(X59,X60,X61,X62) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_28,plain,(
    ! [X63,X64,X65,X66,X67] : k4_enumset1(X63,X63,X64,X65,X66,X67) = k3_enumset1(X63,X64,X65,X66,X67) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_29,plain,(
    ! [X68,X69,X70,X71,X72,X73] : k5_enumset1(X68,X68,X69,X70,X71,X72,X73) = k4_enumset1(X68,X69,X70,X71,X72,X73) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_30,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(X14,k3_xboole_0(X15,X16))
      | r1_tarski(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).

fof(c_0_31,plain,(
    ! [X9,X10] : k3_xboole_0(X9,X10) = k3_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_32,plain,(
    ! [X17,X18] :
      ( ~ r1_tarski(X17,X18)
      | k3_xboole_0(X17,X18) = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38])).

fof(c_0_43,plain,(
    ! [X77,X78] : r1_tarski(k1_tarski(X77),k2_tarski(X77,X78)) ),
    inference(variable_rename,[status(thm)],[t12_zfmisc_1])).

fof(c_0_44,plain,(
    ! [X53] : k2_tarski(X53,X53) = k1_tarski(X53) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_45,plain,(
    ! [X19] : r1_tarski(k1_xboole_0,X19) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)) = k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,plain,
    ( r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_50,plain,(
    ! [X20,X21] : k4_xboole_0(X20,k4_xboole_0(X20,X21)) = k3_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_51,plain,(
    ! [X12,X13] : k4_xboole_0(X12,X13) = k5_xboole_0(X12,k3_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_52,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_53,plain,(
    ! [X7,X8] : k2_xboole_0(X7,X8) = k2_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_54,plain,(
    ! [X23,X24] : k2_xboole_0(X23,X24) = k5_xboole_0(X23,k4_xboole_0(X24,X23)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(X1,k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0))
    | ~ r1_tarski(X1,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,plain,
    ( r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38])).

fof(c_0_57,plain,(
    ! [X45,X46,X47,X48] : k2_enumset1(X45,X46,X47,X48) = k2_xboole_0(k2_tarski(X45,X46),k2_tarski(X47,X48)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_52])).

fof(c_0_61,plain,(
    ! [X22] : k5_xboole_0(X22,k1_xboole_0) = X22 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_62,plain,(
    ! [X11] : k3_xboole_0(X11,X11) = X11 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_63,plain,(
    ! [X49,X50,X51,X52] : k2_enumset1(X49,X50,X51,X52) = k2_xboole_0(k1_enumset1(X49,X50,X51),k1_tarski(X52)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

cnf(c_0_64,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_65,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_67,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_68,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59]),c_0_59])).

cnf(c_0_69,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_60])).

cnf(c_0_70,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

fof(c_0_72,plain,(
    ! [X25,X26,X27,X28,X29,X30,X31,X32,X33,X34] :
      ( ( ~ r2_hidden(X29,X28)
        | X29 = X25
        | X29 = X26
        | X29 = X27
        | X28 != k1_enumset1(X25,X26,X27) )
      & ( X30 != X25
        | r2_hidden(X30,X28)
        | X28 != k1_enumset1(X25,X26,X27) )
      & ( X30 != X26
        | r2_hidden(X30,X28)
        | X28 != k1_enumset1(X25,X26,X27) )
      & ( X30 != X27
        | r2_hidden(X30,X28)
        | X28 != k1_enumset1(X25,X26,X27) )
      & ( esk1_4(X31,X32,X33,X34) != X31
        | ~ r2_hidden(esk1_4(X31,X32,X33,X34),X34)
        | X34 = k1_enumset1(X31,X32,X33) )
      & ( esk1_4(X31,X32,X33,X34) != X32
        | ~ r2_hidden(esk1_4(X31,X32,X33,X34),X34)
        | X34 = k1_enumset1(X31,X32,X33) )
      & ( esk1_4(X31,X32,X33,X34) != X33
        | ~ r2_hidden(esk1_4(X31,X32,X33,X34),X34)
        | X34 = k1_enumset1(X31,X32,X33) )
      & ( r2_hidden(esk1_4(X31,X32,X33,X34),X34)
        | esk1_4(X31,X32,X33,X34) = X31
        | esk1_4(X31,X32,X33,X34) = X32
        | esk1_4(X31,X32,X33,X34) = X33
        | X34 = k1_enumset1(X31,X32,X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_73,plain,(
    ! [X74,X75,X76] : k1_enumset1(X74,X75,X76) = k1_enumset1(X74,X76,X75) ),
    inference(variable_rename,[status(thm)],[t98_enumset1])).

cnf(c_0_74,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_75,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65]),c_0_65]),c_0_59]),c_0_59])).

cnf(c_0_76,negated_conjecture,
    ( k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)) = k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_66])).

cnf(c_0_77,plain,
    ( k5_enumset1(X1,X1,X1,X1,X2,X3,X4) = k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X3,X3,X4),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X3,X3,X4),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_34]),c_0_34]),c_0_65]),c_0_59]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_71])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

fof(c_0_80,plain,(
    ! [X36,X37,X38,X39,X40,X41,X42,X43] :
      ( ( ~ r2_hidden(X39,X38)
        | X39 = X36
        | X39 = X37
        | X38 != k2_tarski(X36,X37) )
      & ( X40 != X36
        | r2_hidden(X40,X38)
        | X38 != k2_tarski(X36,X37) )
      & ( X40 != X37
        | r2_hidden(X40,X38)
        | X38 != k2_tarski(X36,X37) )
      & ( esk2_3(X41,X42,X43) != X41
        | ~ r2_hidden(esk2_3(X41,X42,X43),X43)
        | X43 = k2_tarski(X41,X42) )
      & ( esk2_3(X41,X42,X43) != X42
        | ~ r2_hidden(esk2_3(X41,X42,X43),X43)
        | X43 = k2_tarski(X41,X42) )
      & ( r2_hidden(esk2_3(X41,X42,X43),X43)
        | esk2_3(X41,X42,X43) = X41
        | esk2_3(X41,X42,X43) = X42
        | X43 = k2_tarski(X41,X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_81,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_82,plain,
    ( k5_enumset1(X1,X1,X1,X1,X2,X3,X4) = k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X4),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X4),k5_enumset1(X1,X1,X1,X1,X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_49]),c_0_34]),c_0_65]),c_0_59]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38])).

cnf(c_0_83,negated_conjecture,
    ( k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0) = k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77]),c_0_78]),c_0_70])).

cnf(c_0_84,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X4,X4,X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_85,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_86,plain,
    ( k5_enumset1(X1,X1,X1,X1,X1,X2,X3) = k5_enumset1(X1,X1,X1,X1,X1,X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38])).

cnf(c_0_87,negated_conjecture,
    ( k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0,X1) = k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_82])).

cnf(c_0_88,plain,
    ( r2_hidden(X1,X2)
    | X2 != k5_enumset1(X3,X3,X3,X3,X3,X4,X1) ),
    inference(er,[status(thm)],[c_0_84])).

cnf(c_0_89,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k5_enumset1(X3,X3,X3,X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_90,negated_conjecture,
    ( k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1,esk6_0) = k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(X1,X2)
    | X2 != k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_87])).

cnf(c_0_92,negated_conjecture,
    ( k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0)) = k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_76,c_0_83])).

cnf(c_0_93,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k5_enumset1(X3,X3,X3,X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0,esk5_0) = k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_83,c_0_90])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(X1,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0,X1)) ),
    inference(er,[status(thm)],[c_0_91])).

cnf(c_0_96,negated_conjecture,
    ( k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0,esk3_0) = k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_92]),c_0_78]),c_0_70])).

cnf(c_0_97,negated_conjecture,
    ( X1 = esk5_0
    | X1 = esk6_0
    | ~ r2_hidden(X1,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_90]),c_0_94])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(esk3_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_99,negated_conjecture,
    ( esk3_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_100,negated_conjecture,
    ( esk3_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_101,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99]),c_0_100]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:42:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.13/0.38  # and selection function SelectNegativeLiterals.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t28_zfmisc_1, conjecture, ![X1, X2, X3, X4]:~(((r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))&X1!=X3)&X1!=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 0.13/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.38  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.13/0.38  fof(t18_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k3_xboole_0(X2,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 0.13/0.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.13/0.38  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.13/0.38  fof(t12_zfmisc_1, axiom, ![X1, X2]:r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 0.13/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.13/0.38  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.13/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.38  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.13/0.38  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.13/0.38  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 0.13/0.38  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.13/0.38  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.13/0.38  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 0.13/0.38  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.13/0.38  fof(t98_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X1,X3,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_enumset1)).
% 0.13/0.38  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.13/0.38  fof(c_0_23, negated_conjecture, ~(![X1, X2, X3, X4]:~(((r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))&X1!=X3)&X1!=X4))), inference(assume_negation,[status(cth)],[t28_zfmisc_1])).
% 0.13/0.38  fof(c_0_24, negated_conjecture, ((r1_tarski(k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0))&esk3_0!=esk5_0)&esk3_0!=esk6_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.13/0.38  fof(c_0_25, plain, ![X54, X55]:k1_enumset1(X54,X54,X55)=k2_tarski(X54,X55), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  fof(c_0_26, plain, ![X56, X57, X58]:k2_enumset1(X56,X56,X57,X58)=k1_enumset1(X56,X57,X58), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.38  fof(c_0_27, plain, ![X59, X60, X61, X62]:k3_enumset1(X59,X59,X60,X61,X62)=k2_enumset1(X59,X60,X61,X62), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.38  fof(c_0_28, plain, ![X63, X64, X65, X66, X67]:k4_enumset1(X63,X63,X64,X65,X66,X67)=k3_enumset1(X63,X64,X65,X66,X67), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.38  fof(c_0_29, plain, ![X68, X69, X70, X71, X72, X73]:k5_enumset1(X68,X68,X69,X70,X71,X72,X73)=k4_enumset1(X68,X69,X70,X71,X72,X73), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.13/0.38  fof(c_0_30, plain, ![X14, X15, X16]:(~r1_tarski(X14,k3_xboole_0(X15,X16))|r1_tarski(X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).
% 0.13/0.38  fof(c_0_31, plain, ![X9, X10]:k3_xboole_0(X9,X10)=k3_xboole_0(X10,X9), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.13/0.38  fof(c_0_32, plain, ![X17, X18]:(~r1_tarski(X17,X18)|k3_xboole_0(X17,X18)=X17), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (r1_tarski(k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_34, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_35, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_36, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_37, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.38  cnf(c_0_38, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_39, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_40, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.38  cnf(c_0_41, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (r1_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38])).
% 0.13/0.38  fof(c_0_43, plain, ![X77, X78]:r1_tarski(k1_tarski(X77),k2_tarski(X77,X78)), inference(variable_rename,[status(thm)],[t12_zfmisc_1])).
% 0.13/0.38  fof(c_0_44, plain, ![X53]:k2_tarski(X53,X53)=k1_tarski(X53), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.38  fof(c_0_45, plain, ![X19]:r1_tarski(k1_xboole_0,X19), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.13/0.38  cnf(c_0_46, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0))=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.38  cnf(c_0_48, plain, (r1_tarski(k1_tarski(X1),k2_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.38  cnf(c_0_49, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.38  fof(c_0_50, plain, ![X20, X21]:k4_xboole_0(X20,k4_xboole_0(X20,X21))=k3_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.13/0.38  fof(c_0_51, plain, ![X12, X13]:k4_xboole_0(X12,X13)=k5_xboole_0(X12,k3_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.38  cnf(c_0_52, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.38  fof(c_0_53, plain, ![X7, X8]:k2_xboole_0(X7,X8)=k2_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.13/0.38  fof(c_0_54, plain, ![X23, X24]:k2_xboole_0(X23,X24)=k5_xboole_0(X23,k4_xboole_0(X24,X23)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, (r1_tarski(X1,k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0))|~r1_tarski(X1,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.13/0.38  cnf(c_0_56, plain, (r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38])).
% 0.13/0.38  fof(c_0_57, plain, ![X45, X46, X47, X48]:k2_enumset1(X45,X46,X47,X48)=k2_xboole_0(k2_tarski(X45,X46),k2_tarski(X47,X48)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 0.13/0.38  cnf(c_0_58, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.13/0.38  cnf(c_0_59, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.13/0.38  cnf(c_0_60, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_52])).
% 0.13/0.38  fof(c_0_61, plain, ![X22]:k5_xboole_0(X22,k1_xboole_0)=X22, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.13/0.38  fof(c_0_62, plain, ![X11]:k3_xboole_0(X11,X11)=X11, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.13/0.38  fof(c_0_63, plain, ![X49, X50, X51, X52]:k2_enumset1(X49,X50,X51,X52)=k2_xboole_0(k1_enumset1(X49,X50,X51),k1_tarski(X52)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 0.13/0.38  cnf(c_0_64, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.13/0.38  cnf(c_0_65, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.13/0.38  cnf(c_0_66, negated_conjecture, (r1_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.13/0.38  cnf(c_0_67, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.13/0.38  cnf(c_0_68, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59]), c_0_59])).
% 0.13/0.38  cnf(c_0_69, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_60])).
% 0.13/0.38  cnf(c_0_70, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.13/0.38  cnf(c_0_71, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.13/0.38  fof(c_0_72, plain, ![X25, X26, X27, X28, X29, X30, X31, X32, X33, X34]:(((~r2_hidden(X29,X28)|(X29=X25|X29=X26|X29=X27)|X28!=k1_enumset1(X25,X26,X27))&(((X30!=X25|r2_hidden(X30,X28)|X28!=k1_enumset1(X25,X26,X27))&(X30!=X26|r2_hidden(X30,X28)|X28!=k1_enumset1(X25,X26,X27)))&(X30!=X27|r2_hidden(X30,X28)|X28!=k1_enumset1(X25,X26,X27))))&((((esk1_4(X31,X32,X33,X34)!=X31|~r2_hidden(esk1_4(X31,X32,X33,X34),X34)|X34=k1_enumset1(X31,X32,X33))&(esk1_4(X31,X32,X33,X34)!=X32|~r2_hidden(esk1_4(X31,X32,X33,X34),X34)|X34=k1_enumset1(X31,X32,X33)))&(esk1_4(X31,X32,X33,X34)!=X33|~r2_hidden(esk1_4(X31,X32,X33,X34),X34)|X34=k1_enumset1(X31,X32,X33)))&(r2_hidden(esk1_4(X31,X32,X33,X34),X34)|(esk1_4(X31,X32,X33,X34)=X31|esk1_4(X31,X32,X33,X34)=X32|esk1_4(X31,X32,X33,X34)=X33)|X34=k1_enumset1(X31,X32,X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.13/0.38  fof(c_0_73, plain, ![X74, X75, X76]:k1_enumset1(X74,X75,X76)=k1_enumset1(X74,X76,X75), inference(variable_rename,[status(thm)],[t98_enumset1])).
% 0.13/0.38  cnf(c_0_74, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.13/0.38  cnf(c_0_75, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65]), c_0_65]), c_0_59]), c_0_59])).
% 0.13/0.38  cnf(c_0_76, negated_conjecture, (k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0))=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_41, c_0_66])).
% 0.13/0.38  cnf(c_0_77, plain, (k5_enumset1(X1,X1,X1,X1,X2,X3,X4)=k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X3,X3,X4),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X3,X3,X4),k5_enumset1(X1,X1,X1,X1,X1,X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_34]), c_0_34]), c_0_65]), c_0_59]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38])).
% 0.13/0.38  cnf(c_0_78, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_71])).
% 0.13/0.38  cnf(c_0_79, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.13/0.38  fof(c_0_80, plain, ![X36, X37, X38, X39, X40, X41, X42, X43]:(((~r2_hidden(X39,X38)|(X39=X36|X39=X37)|X38!=k2_tarski(X36,X37))&((X40!=X36|r2_hidden(X40,X38)|X38!=k2_tarski(X36,X37))&(X40!=X37|r2_hidden(X40,X38)|X38!=k2_tarski(X36,X37))))&(((esk2_3(X41,X42,X43)!=X41|~r2_hidden(esk2_3(X41,X42,X43),X43)|X43=k2_tarski(X41,X42))&(esk2_3(X41,X42,X43)!=X42|~r2_hidden(esk2_3(X41,X42,X43),X43)|X43=k2_tarski(X41,X42)))&(r2_hidden(esk2_3(X41,X42,X43),X43)|(esk2_3(X41,X42,X43)=X41|esk2_3(X41,X42,X43)=X42)|X43=k2_tarski(X41,X42)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.13/0.38  cnf(c_0_81, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.13/0.38  cnf(c_0_82, plain, (k5_enumset1(X1,X1,X1,X1,X2,X3,X4)=k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X4),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X4),k5_enumset1(X1,X1,X1,X1,X1,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_49]), c_0_34]), c_0_65]), c_0_59]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38])).
% 0.13/0.38  cnf(c_0_83, negated_conjecture, (k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77]), c_0_78]), c_0_70])).
% 0.13/0.38  cnf(c_0_84, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X4,X4,X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 0.13/0.38  cnf(c_0_85, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.13/0.38  cnf(c_0_86, plain, (k5_enumset1(X1,X1,X1,X1,X1,X2,X3)=k5_enumset1(X1,X1,X1,X1,X1,X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38])).
% 0.13/0.38  cnf(c_0_87, negated_conjecture, (k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0,X1)=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_82])).
% 0.13/0.38  cnf(c_0_88, plain, (r2_hidden(X1,X2)|X2!=k5_enumset1(X3,X3,X3,X3,X3,X4,X1)), inference(er,[status(thm)],[c_0_84])).
% 0.13/0.38  cnf(c_0_89, plain, (X1=X4|X1=X3|X2!=k5_enumset1(X3,X3,X3,X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 0.13/0.38  cnf(c_0_90, negated_conjecture, (k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1,esk6_0)=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0,X1)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.13/0.38  cnf(c_0_91, negated_conjecture, (r2_hidden(X1,X2)|X2!=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0,X1)), inference(spm,[status(thm)],[c_0_88, c_0_87])).
% 0.13/0.38  cnf(c_0_92, negated_conjecture, (k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0))=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[c_0_76, c_0_83])).
% 0.13/0.38  cnf(c_0_93, plain, (X1=X2|X1=X3|~r2_hidden(X1,k5_enumset1(X3,X3,X3,X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_89])).
% 0.13/0.38  cnf(c_0_94, negated_conjecture, (k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0,esk5_0)=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_83, c_0_90])).
% 0.13/0.38  cnf(c_0_95, negated_conjecture, (r2_hidden(X1,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0,X1))), inference(er,[status(thm)],[c_0_91])).
% 0.13/0.38  cnf(c_0_96, negated_conjecture, (k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0,esk3_0)=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_92]), c_0_78]), c_0_70])).
% 0.13/0.38  cnf(c_0_97, negated_conjecture, (X1=esk5_0|X1=esk6_0|~r2_hidden(X1,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_90]), c_0_94])).
% 0.13/0.38  cnf(c_0_98, negated_conjecture, (r2_hidden(esk3_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.13/0.38  cnf(c_0_99, negated_conjecture, (esk3_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_100, negated_conjecture, (esk3_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_101, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_99]), c_0_100]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 102
% 0.13/0.38  # Proof object clause steps            : 55
% 0.13/0.38  # Proof object formula steps           : 47
% 0.13/0.38  # Proof object conjectures             : 22
% 0.13/0.38  # Proof object clause conjectures      : 19
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 25
% 0.13/0.38  # Proof object initial formulas used   : 23
% 0.13/0.38  # Proof object generating inferences   : 18
% 0.13/0.38  # Proof object simplifying inferences  : 104
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 23
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 37
% 0.13/0.38  # Removed in clause preprocessing      : 8
% 0.13/0.38  # Initial clauses in saturation        : 29
% 0.13/0.38  # Processed clauses                    : 108
% 0.13/0.38  # ...of these trivial                  : 12
% 0.13/0.38  # ...subsumed                          : 27
% 0.13/0.38  # ...remaining for further processing  : 69
% 0.13/0.38  # Other redundant clauses eliminated   : 15
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 6
% 0.13/0.38  # Generated clauses                    : 524
% 0.13/0.38  # ...of the previous two non-trivial   : 438
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 501
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 23
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 58
% 0.13/0.38  #    Positive orientable unit clauses  : 29
% 0.13/0.38  #    Positive unorientable unit clauses: 3
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 24
% 0.13/0.38  # Current number of unprocessed clauses: 352
% 0.13/0.38  # ...number of literals in the above   : 1429
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 14
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 127
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 120
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 27
% 0.13/0.38  # Unit Clause-clause subsumption calls : 3
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 50
% 0.13/0.38  # BW rewrite match successes           : 14
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 9891
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.040 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.044 s
% 0.13/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
