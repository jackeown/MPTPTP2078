%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:38:27 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  102 (3164 expanded)
%              Number of clauses        :   57 (1142 expanded)
%              Number of leaves         :   22 (1007 expanded)
%              Depth                    :   15
%              Number of atoms          :  168 (3337 expanded)
%              Number of equality atoms :  123 (3157 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t24_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),k1_tarski(X2))
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_zfmisc_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

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

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(t102_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_enumset1)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(c_0_22,plain,(
    ! [X20,X21] : r1_xboole_0(k4_xboole_0(X20,X21),X21) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_23,plain,(
    ! [X13,X14] : k4_xboole_0(X13,X14) = k5_xboole_0(X13,k3_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_24,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_26,plain,(
    ! [X10] : k3_xboole_0(X10,X10) = X10 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(k1_tarski(X1),k1_tarski(X2))
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t24_zfmisc_1])).

fof(c_0_28,plain,(
    ! [X11,X12] :
      ( ~ r1_xboole_0(X11,X12)
      | r1_xboole_0(X12,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_29,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_31,plain,(
    ! [X22,X23] : k2_xboole_0(X22,X23) = k5_xboole_0(X22,k4_xboole_0(X23,X22)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_32,negated_conjecture,
    ( r1_tarski(k1_tarski(esk2_0),k1_tarski(esk3_0))
    & esk2_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

fof(c_0_33,plain,(
    ! [X47] : k2_tarski(X47,X47) = k1_tarski(X47) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_34,plain,(
    ! [X48,X49] : k1_enumset1(X48,X48,X49) = k2_tarski(X48,X49) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_35,plain,(
    ! [X50,X51,X52] : k2_enumset1(X50,X50,X51,X52) = k1_enumset1(X50,X51,X52) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_36,plain,(
    ! [X53,X54,X55,X56] : k3_enumset1(X53,X53,X54,X55,X56) = k2_enumset1(X53,X54,X55,X56) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_37,plain,(
    ! [X57,X58,X59,X60,X61] : k4_enumset1(X57,X57,X58,X59,X60,X61) = k3_enumset1(X57,X58,X59,X60,X61) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_38,plain,(
    ! [X62,X63,X64,X65,X66,X67] : k5_enumset1(X62,X62,X63,X64,X65,X66,X67) = k4_enumset1(X62,X63,X64,X65,X66,X67) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_39,plain,(
    ! [X68,X69,X70,X71,X72,X73,X74] : k6_enumset1(X68,X68,X69,X70,X71,X72,X73,X74) = k5_enumset1(X68,X69,X70,X71,X72,X73,X74) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_40,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,X18)) = k3_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_41,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,plain,
    ( r1_xboole_0(k5_xboole_0(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_44,plain,(
    ! [X40,X41,X42] : k1_enumset1(X40,X41,X42) = k2_xboole_0(k1_tarski(X40),k2_tarski(X41,X42)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_46,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k3_xboole_0(X15,X16) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k1_tarski(esk2_0),k1_tarski(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_48,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_49,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_50,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_51,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_52,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_53,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_54,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_57,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_58,plain,(
    ! [X19] : k5_xboole_0(X19,k1_xboole_0) = X19 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_59,plain,(
    ! [X35,X36,X37] : k1_enumset1(X35,X36,X37) = k1_enumset1(X37,X36,X35) ),
    inference(variable_rename,[status(thm)],[t102_enumset1])).

fof(c_0_60,plain,(
    ! [X43,X44,X45,X46] : k2_enumset1(X43,X44,X45,X46) = k2_xboole_0(k1_enumset1(X43,X44,X45),k1_tarski(X46)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

cnf(c_0_61,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_62,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_45,c_0_25])).

cnf(c_0_63,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_54]),c_0_54])).

cnf(c_0_65,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_25]),c_0_25])).

cnf(c_0_66,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_68,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_69,plain,(
    ! [X38,X39] : k2_tarski(X38,X39) = k2_xboole_0(k1_tarski(X38),k1_tarski(X39)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_70,plain,(
    ! [X24,X25,X26,X27,X28,X29,X30,X31,X32,X33] :
      ( ( ~ r2_hidden(X28,X27)
        | X28 = X24
        | X28 = X25
        | X28 = X26
        | X27 != k1_enumset1(X24,X25,X26) )
      & ( X29 != X24
        | r2_hidden(X29,X27)
        | X27 != k1_enumset1(X24,X25,X26) )
      & ( X29 != X25
        | r2_hidden(X29,X27)
        | X27 != k1_enumset1(X24,X25,X26) )
      & ( X29 != X26
        | r2_hidden(X29,X27)
        | X27 != k1_enumset1(X24,X25,X26) )
      & ( esk1_4(X30,X31,X32,X33) != X30
        | ~ r2_hidden(esk1_4(X30,X31,X32,X33),X33)
        | X33 = k1_enumset1(X30,X31,X32) )
      & ( esk1_4(X30,X31,X32,X33) != X31
        | ~ r2_hidden(esk1_4(X30,X31,X32,X33),X33)
        | X33 = k1_enumset1(X30,X31,X32) )
      & ( esk1_4(X30,X31,X32,X33) != X32
        | ~ r2_hidden(esk1_4(X30,X31,X32,X33),X33)
        | X33 = k1_enumset1(X30,X31,X32) )
      & ( r2_hidden(esk1_4(X30,X31,X32,X33),X33)
        | esk1_4(X30,X31,X32,X33) = X30
        | esk1_4(X30,X31,X32,X33) = X31
        | esk1_4(X30,X31,X32,X33) = X32
        | X33 = k1_enumset1(X30,X31,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_71,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_72,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_48]),c_0_49]),c_0_49]),c_0_62]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54])).

cnf(c_0_73,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_74,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_30])).

cnf(c_0_75,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_54]),c_0_54])).

cnf(c_0_76,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X2,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_78,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),k3_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_48]),c_0_49]),c_0_62]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54])).

cnf(c_0_79,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74]),c_0_67]),c_0_75])).

cnf(c_0_80,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_81,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_49]),c_0_62]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54])).

cnf(c_0_82,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X4,X4,X4,X2,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_50]),c_0_51]),c_0_52]),c_0_53]),c_0_54])).

cnf(c_0_83,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_78])).

cnf(c_0_84,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_50]),c_0_51]),c_0_52]),c_0_53]),c_0_54])).

cnf(c_0_85,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) ),
    inference(rw,[status(thm)],[c_0_81,c_0_72])).

cnf(c_0_86,plain,
    ( r2_hidden(X1,X2)
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X1,X4) ),
    inference(er,[status(thm)],[c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1,X2) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_83]),c_0_78])).

cnf(c_0_88,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_73,c_0_79])).

cnf(c_0_89,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k6_enumset1(X4,X4,X4,X4,X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_84])).

cnf(c_0_90,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1,X1) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_83])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(X1,X2)
    | X2 != k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1,X3) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_92,negated_conjecture,
    ( k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk2_0) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_88]),c_0_74]),c_0_67])).

cnf(c_0_93,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X3)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_85])).

cnf(c_0_94,negated_conjecture,
    ( k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1,X1) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1) ),
    inference(rw,[status(thm)],[c_0_90,c_0_87])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(X1,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1,X2)) ),
    inference(er,[status(thm)],[c_0_91])).

cnf(c_0_96,negated_conjecture,
    ( k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk2_0,X1) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_92]),c_0_78])).

cnf(c_0_97,negated_conjecture,
    ( X1 = esk3_0
    | X1 = X2
    | ~ r2_hidden(X1,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_87]),c_0_94])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(esk2_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_99,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_100,negated_conjecture,
    ( esk2_0 = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99])).

cnf(c_0_101,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_100])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.34  % Computer   : n024.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:22:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.15/0.39  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.15/0.39  # and selection function SelectNegativeLiterals.
% 0.15/0.39  #
% 0.15/0.39  # Preprocessing time       : 0.028 s
% 0.15/0.39  
% 0.15/0.39  # Proof found!
% 0.15/0.39  # SZS status Theorem
% 0.15/0.39  # SZS output start CNFRefutation
% 0.15/0.39  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.15/0.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.15/0.39  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.15/0.39  fof(t24_zfmisc_1, conjecture, ![X1, X2]:(r1_tarski(k1_tarski(X1),k1_tarski(X2))=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 0.15/0.39  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.15/0.39  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.15/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.15/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.15/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.15/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.15/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.15/0.39  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.15/0.39  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.15/0.39  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.15/0.39  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.15/0.39  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 0.15/0.39  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.15/0.39  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.15/0.39  fof(t102_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X3,X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_enumset1)).
% 0.15/0.39  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 0.15/0.39  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.15/0.39  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.15/0.39  fof(c_0_22, plain, ![X20, X21]:r1_xboole_0(k4_xboole_0(X20,X21),X21), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.15/0.39  fof(c_0_23, plain, ![X13, X14]:k4_xboole_0(X13,X14)=k5_xboole_0(X13,k3_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.21/0.39  cnf(c_0_24, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.39  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.39  fof(c_0_26, plain, ![X10]:k3_xboole_0(X10,X10)=X10, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.21/0.39  fof(c_0_27, negated_conjecture, ~(![X1, X2]:(r1_tarski(k1_tarski(X1),k1_tarski(X2))=>X1=X2)), inference(assume_negation,[status(cth)],[t24_zfmisc_1])).
% 0.21/0.39  fof(c_0_28, plain, ![X11, X12]:(~r1_xboole_0(X11,X12)|r1_xboole_0(X12,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.21/0.39  cnf(c_0_29, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.21/0.39  cnf(c_0_30, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.39  fof(c_0_31, plain, ![X22, X23]:k2_xboole_0(X22,X23)=k5_xboole_0(X22,k4_xboole_0(X23,X22)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.21/0.39  fof(c_0_32, negated_conjecture, (r1_tarski(k1_tarski(esk2_0),k1_tarski(esk3_0))&esk2_0!=esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).
% 0.21/0.39  fof(c_0_33, plain, ![X47]:k2_tarski(X47,X47)=k1_tarski(X47), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.39  fof(c_0_34, plain, ![X48, X49]:k1_enumset1(X48,X48,X49)=k2_tarski(X48,X49), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.39  fof(c_0_35, plain, ![X50, X51, X52]:k2_enumset1(X50,X50,X51,X52)=k1_enumset1(X50,X51,X52), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.39  fof(c_0_36, plain, ![X53, X54, X55, X56]:k3_enumset1(X53,X53,X54,X55,X56)=k2_enumset1(X53,X54,X55,X56), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.21/0.39  fof(c_0_37, plain, ![X57, X58, X59, X60, X61]:k4_enumset1(X57,X57,X58,X59,X60,X61)=k3_enumset1(X57,X58,X59,X60,X61), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.21/0.39  fof(c_0_38, plain, ![X62, X63, X64, X65, X66, X67]:k5_enumset1(X62,X62,X63,X64,X65,X66,X67)=k4_enumset1(X62,X63,X64,X65,X66,X67), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.21/0.39  fof(c_0_39, plain, ![X68, X69, X70, X71, X72, X73, X74]:k6_enumset1(X68,X68,X69,X70,X71,X72,X73,X74)=k5_enumset1(X68,X69,X70,X71,X72,X73,X74), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.21/0.39  fof(c_0_40, plain, ![X17, X18]:k4_xboole_0(X17,k4_xboole_0(X17,X18))=k3_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.21/0.39  fof(c_0_41, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.21/0.39  cnf(c_0_42, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.39  cnf(c_0_43, plain, (r1_xboole_0(k5_xboole_0(X1,X1),X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.21/0.39  fof(c_0_44, plain, ![X40, X41, X42]:k1_enumset1(X40,X41,X42)=k2_xboole_0(k1_tarski(X40),k2_tarski(X41,X42)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.21/0.39  cnf(c_0_45, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.39  fof(c_0_46, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k3_xboole_0(X15,X16)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.21/0.39  cnf(c_0_47, negated_conjecture, (r1_tarski(k1_tarski(esk2_0),k1_tarski(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.39  cnf(c_0_48, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.39  cnf(c_0_49, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.39  cnf(c_0_50, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.39  cnf(c_0_51, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.39  cnf(c_0_52, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.39  cnf(c_0_53, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.39  cnf(c_0_54, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.39  cnf(c_0_55, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.39  cnf(c_0_56, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.39  cnf(c_0_57, plain, (r1_xboole_0(X1,k5_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.21/0.39  fof(c_0_58, plain, ![X19]:k5_xboole_0(X19,k1_xboole_0)=X19, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.21/0.39  fof(c_0_59, plain, ![X35, X36, X37]:k1_enumset1(X35,X36,X37)=k1_enumset1(X37,X36,X35), inference(variable_rename,[status(thm)],[t102_enumset1])).
% 0.21/0.39  fof(c_0_60, plain, ![X43, X44, X45, X46]:k2_enumset1(X43,X44,X45,X46)=k2_xboole_0(k1_enumset1(X43,X44,X45),k1_tarski(X46)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 0.21/0.39  cnf(c_0_61, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.39  cnf(c_0_62, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_45, c_0_25])).
% 0.21/0.39  cnf(c_0_63, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.39  cnf(c_0_64, negated_conjecture, (r1_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_52]), c_0_52]), c_0_53]), c_0_53]), c_0_54]), c_0_54])).
% 0.21/0.39  cnf(c_0_65, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_25]), c_0_25])).
% 0.21/0.39  cnf(c_0_66, plain, (k3_xboole_0(X1,k5_xboole_0(X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.21/0.39  cnf(c_0_67, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.21/0.39  cnf(c_0_68, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.21/0.39  fof(c_0_69, plain, ![X38, X39]:k2_tarski(X38,X39)=k2_xboole_0(k1_tarski(X38),k1_tarski(X39)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.21/0.39  fof(c_0_70, plain, ![X24, X25, X26, X27, X28, X29, X30, X31, X32, X33]:(((~r2_hidden(X28,X27)|(X28=X24|X28=X25|X28=X26)|X27!=k1_enumset1(X24,X25,X26))&(((X29!=X24|r2_hidden(X29,X27)|X27!=k1_enumset1(X24,X25,X26))&(X29!=X25|r2_hidden(X29,X27)|X27!=k1_enumset1(X24,X25,X26)))&(X29!=X26|r2_hidden(X29,X27)|X27!=k1_enumset1(X24,X25,X26))))&((((esk1_4(X30,X31,X32,X33)!=X30|~r2_hidden(esk1_4(X30,X31,X32,X33),X33)|X33=k1_enumset1(X30,X31,X32))&(esk1_4(X30,X31,X32,X33)!=X31|~r2_hidden(esk1_4(X30,X31,X32,X33),X33)|X33=k1_enumset1(X30,X31,X32)))&(esk1_4(X30,X31,X32,X33)!=X32|~r2_hidden(esk1_4(X30,X31,X32,X33),X33)|X33=k1_enumset1(X30,X31,X32)))&(r2_hidden(esk1_4(X30,X31,X32,X33),X33)|(esk1_4(X30,X31,X32,X33)=X30|esk1_4(X30,X31,X32,X33)=X31|esk1_4(X30,X31,X32,X33)=X32)|X33=k1_enumset1(X30,X31,X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.21/0.39  cnf(c_0_71, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.21/0.39  cnf(c_0_72, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_48]), c_0_49]), c_0_49]), c_0_62]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_54]), c_0_54]), c_0_54]), c_0_54]), c_0_54])).
% 0.21/0.39  cnf(c_0_73, negated_conjecture, (k3_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.21/0.39  cnf(c_0_74, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_30])).
% 0.21/0.39  cnf(c_0_75, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_52]), c_0_52]), c_0_53]), c_0_53]), c_0_54]), c_0_54])).
% 0.21/0.39  cnf(c_0_76, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.21/0.39  cnf(c_0_77, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X2,X5)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.21/0.39  cnf(c_0_78, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),k3_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_48]), c_0_49]), c_0_62]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_54]), c_0_54]), c_0_54]), c_0_54]), c_0_54])).
% 0.21/0.39  cnf(c_0_79, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74]), c_0_67]), c_0_75])).
% 0.21/0.39  cnf(c_0_80, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.21/0.39  cnf(c_0_81, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_49]), c_0_62]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_54]), c_0_54]), c_0_54]), c_0_54]), c_0_54])).
% 0.21/0.39  cnf(c_0_82, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X4,X4,X4,X2,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_50]), c_0_51]), c_0_52]), c_0_53]), c_0_54])).
% 0.21/0.39  cnf(c_0_83, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1)=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_78])).
% 0.21/0.39  cnf(c_0_84, plain, (X1=X5|X1=X4|X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_50]), c_0_51]), c_0_52]), c_0_53]), c_0_54])).
% 0.21/0.39  cnf(c_0_85, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X2)=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)), inference(rw,[status(thm)],[c_0_81, c_0_72])).
% 0.21/0.39  cnf(c_0_86, plain, (r2_hidden(X1,X2)|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X1,X4)), inference(er,[status(thm)],[c_0_82])).
% 0.21/0.39  cnf(c_0_87, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1,X2)=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_83]), c_0_78])).
% 0.21/0.39  cnf(c_0_88, negated_conjecture, (k3_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0))=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[c_0_73, c_0_79])).
% 0.21/0.39  cnf(c_0_89, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k6_enumset1(X4,X4,X4,X4,X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_84])).
% 0.21/0.39  cnf(c_0_90, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1,X1)=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1)), inference(spm,[status(thm)],[c_0_85, c_0_83])).
% 0.21/0.39  cnf(c_0_91, negated_conjecture, (r2_hidden(X1,X2)|X2!=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1,X3)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.21/0.39  cnf(c_0_92, negated_conjecture, (k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk2_0)=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_88]), c_0_74]), c_0_67])).
% 0.21/0.39  cnf(c_0_93, plain, (X1=X2|X1=X3|~r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X3))), inference(spm,[status(thm)],[c_0_89, c_0_85])).
% 0.21/0.39  cnf(c_0_94, negated_conjecture, (k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1,X1)=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1)), inference(rw,[status(thm)],[c_0_90, c_0_87])).
% 0.21/0.39  cnf(c_0_95, negated_conjecture, (r2_hidden(X1,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1,X2))), inference(er,[status(thm)],[c_0_91])).
% 0.21/0.39  cnf(c_0_96, negated_conjecture, (k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk2_0,X1)=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_92]), c_0_78])).
% 0.21/0.39  cnf(c_0_97, negated_conjecture, (X1=esk3_0|X1=X2|~r2_hidden(X1,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_87]), c_0_94])).
% 0.21/0.39  cnf(c_0_98, negated_conjecture, (r2_hidden(esk2_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1))), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.21/0.39  cnf(c_0_99, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.39  cnf(c_0_100, negated_conjecture, (esk2_0=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_99])).
% 0.21/0.39  cnf(c_0_101, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_100])]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 102
% 0.21/0.39  # Proof object clause steps            : 57
% 0.21/0.39  # Proof object formula steps           : 45
% 0.21/0.39  # Proof object conjectures             : 21
% 0.21/0.39  # Proof object clause conjectures      : 18
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 24
% 0.21/0.39  # Proof object initial formulas used   : 22
% 0.21/0.39  # Proof object generating inferences   : 18
% 0.21/0.39  # Proof object simplifying inferences  : 143
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 22
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 31
% 0.21/0.39  # Removed in clause preprocessing      : 9
% 0.21/0.39  # Initial clauses in saturation        : 22
% 0.21/0.39  # Processed clauses                    : 128
% 0.21/0.39  # ...of these trivial                  : 13
% 0.21/0.39  # ...subsumed                          : 43
% 0.21/0.39  # ...remaining for further processing  : 72
% 0.21/0.39  # Other redundant clauses eliminated   : 7
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 0
% 0.21/0.39  # Backward-rewritten                   : 64
% 0.21/0.39  # Generated clauses                    : 475
% 0.21/0.39  # ...of the previous two non-trivial   : 362
% 0.21/0.39  # Contextual simplify-reflections      : 0
% 0.21/0.39  # Paramodulations                      : 460
% 0.21/0.39  # Factorizations                       : 0
% 0.21/0.39  # Equation resolutions                 : 15
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 5
% 0.21/0.39  #    Positive orientable unit clauses  : 2
% 0.21/0.39  #    Positive unorientable unit clauses: 1
% 0.21/0.39  #    Negative unit clauses             : 0
% 0.21/0.39  #    Non-unit-clauses                  : 2
% 0.21/0.39  # Current number of unprocessed clauses: 214
% 0.21/0.39  # ...number of literals in the above   : 805
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 73
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 129
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 124
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 43
% 0.21/0.39  # Unit Clause-clause subsumption calls : 12
% 0.21/0.39  # Rewrite failures with RHS unbound    : 5
% 0.21/0.39  # BW rewrite match attempts            : 142
% 0.21/0.39  # BW rewrite match successes           : 77
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 8010
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.038 s
% 0.21/0.39  # System time              : 0.005 s
% 0.21/0.39  # Total time               : 0.043 s
% 0.21/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
