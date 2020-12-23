%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:40:22 EST 2020

% Result     : Theorem 0.48s
% Output     : CNFRefutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 769 expanded)
%              Number of clauses        :   39 ( 301 expanded)
%              Number of leaves         :   16 ( 233 expanded)
%              Depth                    :    8
%              Number of atoms          :   93 ( 811 expanded)
%              Number of equality atoms :   62 ( 760 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t46_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(c_0_16,plain,(
    ! [X64,X65] : k3_tarski(k2_tarski(X64,X65)) = k2_xboole_0(X64,X65) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_17,plain,(
    ! [X48,X49] : k1_enumset1(X48,X48,X49) = k2_tarski(X48,X49) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,plain,(
    ! [X30,X31] :
      ( ( r1_tarski(X30,X31)
        | X30 != X31 )
      & ( r1_tarski(X31,X30)
        | X30 != X31 )
      & ( ~ r1_tarski(X30,X31)
        | ~ r1_tarski(X31,X30)
        | X30 = X31 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_19,plain,(
    ! [X34] : k2_xboole_0(X34,k1_xboole_0) = X34 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_20,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X50,X51,X52] : k2_enumset1(X50,X50,X51,X52) = k1_enumset1(X50,X51,X52) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_23,plain,(
    ! [X53,X54,X55,X56] : k3_enumset1(X53,X53,X54,X55,X56) = k2_enumset1(X53,X54,X55,X56) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_24,plain,(
    ! [X57,X58,X59,X60,X61] : k4_enumset1(X57,X57,X58,X59,X60,X61) = k3_enumset1(X57,X58,X59,X60,X61) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_25,plain,(
    ! [X45,X46] : k2_tarski(X45,X46) = k2_tarski(X46,X45) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_26,plain,(
    ! [X41,X42] : r1_tarski(X41,k2_xboole_0(X41,X42)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_27,plain,(
    ! [X37,X38] : k2_xboole_0(X37,k4_xboole_0(X38,X37)) = k2_xboole_0(X37,X38) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_28,plain,(
    ! [X32,X33] : k4_xboole_0(X32,X33) = k5_xboole_0(X32,k3_xboole_0(X32,X33)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_29,plain,(
    ! [X35,X36] :
      ( ~ r1_tarski(X35,X36)
      | k3_xboole_0(X35,X36) = X35 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_31,plain,(
    ! [X62,X63] :
      ( ( ~ r1_tarski(k1_tarski(X62),X63)
        | r2_hidden(X62,X63) )
      & ( ~ r2_hidden(X62,X63)
        | r1_tarski(k1_tarski(X62),X63) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_32,plain,(
    ! [X47] : k2_tarski(X47,X47) = k1_tarski(X47) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_33,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r2_hidden(X1,X2)
       => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    inference(assume_negation,[status(cth)],[t46_zfmisc_1])).

fof(c_0_34,plain,(
    ! [X39,X40] : k4_xboole_0(k2_xboole_0(X39,X40),X40) = k4_xboole_0(X39,X40) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_36,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_37,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_39,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_40,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_46,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_47,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_48,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0)
    & k2_xboole_0(k1_tarski(esk5_0),esk6_0) != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).

cnf(c_0_49,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_50,plain,
    ( k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_51,plain,
    ( k4_enumset1(X1,X1,X1,X1,X1,X2) = k4_enumset1(X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_21]),c_0_21]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_53,plain,
    ( k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_36]),c_0_36]),c_0_43]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39])).

cnf(c_0_54,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_55,plain,
    ( r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_21]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,plain,
    ( k5_xboole_0(k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)),k3_xboole_0(k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)),X2)) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_36]),c_0_43]),c_0_43]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39])).

cnf(c_0_58,plain,
    ( k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,plain,
    ( k3_xboole_0(X1,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))) = X1 ),
    inference(spm,[status(thm)],[c_0_44,c_0_52])).

cnf(c_0_60,plain,
    ( k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k5_xboole_0(X1,X1))) = k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk5_0),esk6_0) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,plain,
    ( k5_xboole_0(k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)),k3_xboole_0(k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)),k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_53])).

cnf(c_0_64,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_58]),c_0_58])).

cnf(c_0_65,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_58])).

cnf(c_0_66,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_58]),c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( k3_tarski(k4_enumset1(k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)) != esk6_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_47]),c_0_21]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39])).

cnf(c_0_68,negated_conjecture,
    ( k3_xboole_0(k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0) = k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_62])).

cnf(c_0_69,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_58]),c_0_58]),c_0_54]),c_0_65]),c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( k3_tarski(k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) != esk6_0 ),
    inference(rw,[status(thm)],[c_0_67,c_0_51])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_68]),c_0_69]),c_0_51]),c_0_58]),c_0_70]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:22:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.48/0.66  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.48/0.66  # and selection function SelectNegativeLiterals.
% 0.48/0.66  #
% 0.48/0.66  # Preprocessing time       : 0.028 s
% 0.48/0.66  # Presaturation interreduction done
% 0.48/0.66  
% 0.48/0.66  # Proof found!
% 0.48/0.66  # SZS status Theorem
% 0.48/0.66  # SZS output start CNFRefutation
% 0.48/0.66  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.48/0.66  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.48/0.66  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.48/0.66  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.48/0.66  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.48/0.66  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.48/0.66  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.48/0.66  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.48/0.66  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.48/0.66  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.48/0.66  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.48/0.66  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.48/0.66  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.48/0.66  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.48/0.66  fof(t46_zfmisc_1, conjecture, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 0.48/0.66  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.48/0.66  fof(c_0_16, plain, ![X64, X65]:k3_tarski(k2_tarski(X64,X65))=k2_xboole_0(X64,X65), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.48/0.66  fof(c_0_17, plain, ![X48, X49]:k1_enumset1(X48,X48,X49)=k2_tarski(X48,X49), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.48/0.66  fof(c_0_18, plain, ![X30, X31]:(((r1_tarski(X30,X31)|X30!=X31)&(r1_tarski(X31,X30)|X30!=X31))&(~r1_tarski(X30,X31)|~r1_tarski(X31,X30)|X30=X31)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.48/0.66  fof(c_0_19, plain, ![X34]:k2_xboole_0(X34,k1_xboole_0)=X34, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.48/0.66  cnf(c_0_20, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.48/0.66  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.48/0.66  fof(c_0_22, plain, ![X50, X51, X52]:k2_enumset1(X50,X50,X51,X52)=k1_enumset1(X50,X51,X52), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.48/0.66  fof(c_0_23, plain, ![X53, X54, X55, X56]:k3_enumset1(X53,X53,X54,X55,X56)=k2_enumset1(X53,X54,X55,X56), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.48/0.66  fof(c_0_24, plain, ![X57, X58, X59, X60, X61]:k4_enumset1(X57,X57,X58,X59,X60,X61)=k3_enumset1(X57,X58,X59,X60,X61), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.48/0.66  fof(c_0_25, plain, ![X45, X46]:k2_tarski(X45,X46)=k2_tarski(X46,X45), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.48/0.66  fof(c_0_26, plain, ![X41, X42]:r1_tarski(X41,k2_xboole_0(X41,X42)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.48/0.66  fof(c_0_27, plain, ![X37, X38]:k2_xboole_0(X37,k4_xboole_0(X38,X37))=k2_xboole_0(X37,X38), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.48/0.66  fof(c_0_28, plain, ![X32, X33]:k4_xboole_0(X32,X33)=k5_xboole_0(X32,k3_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.48/0.66  fof(c_0_29, plain, ![X35, X36]:(~r1_tarski(X35,X36)|k3_xboole_0(X35,X36)=X35), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.48/0.66  cnf(c_0_30, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.48/0.66  fof(c_0_31, plain, ![X62, X63]:((~r1_tarski(k1_tarski(X62),X63)|r2_hidden(X62,X63))&(~r2_hidden(X62,X63)|r1_tarski(k1_tarski(X62),X63))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.48/0.66  fof(c_0_32, plain, ![X47]:k2_tarski(X47,X47)=k1_tarski(X47), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.48/0.66  fof(c_0_33, negated_conjecture, ~(![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2)), inference(assume_negation,[status(cth)],[t46_zfmisc_1])).
% 0.48/0.66  fof(c_0_34, plain, ![X39, X40]:k4_xboole_0(k2_xboole_0(X39,X40),X40)=k4_xboole_0(X39,X40), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.48/0.66  cnf(c_0_35, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.48/0.66  cnf(c_0_36, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.48/0.66  cnf(c_0_37, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.48/0.66  cnf(c_0_38, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.48/0.66  cnf(c_0_39, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.48/0.66  cnf(c_0_40, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.48/0.66  cnf(c_0_41, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.48/0.66  cnf(c_0_42, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.48/0.66  cnf(c_0_43, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.48/0.66  cnf(c_0_44, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.48/0.66  cnf(c_0_45, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_30])).
% 0.48/0.66  cnf(c_0_46, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.48/0.66  cnf(c_0_47, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.48/0.66  fof(c_0_48, negated_conjecture, (r2_hidden(esk5_0,esk6_0)&k2_xboole_0(k1_tarski(esk5_0),esk6_0)!=esk6_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).
% 0.48/0.66  cnf(c_0_49, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.48/0.66  cnf(c_0_50, plain, (k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.48/0.66  cnf(c_0_51, plain, (k4_enumset1(X1,X1,X1,X1,X1,X2)=k4_enumset1(X2,X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_21]), c_0_21]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 0.48/0.66  cnf(c_0_52, plain, (r1_tarski(X1,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.48/0.66  cnf(c_0_53, plain, (k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_36]), c_0_36]), c_0_43]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 0.48/0.66  cnf(c_0_54, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.48/0.66  cnf(c_0_55, plain, (r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_21]), c_0_37]), c_0_38]), c_0_39])).
% 0.48/0.66  cnf(c_0_56, negated_conjecture, (r2_hidden(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.48/0.66  cnf(c_0_57, plain, (k5_xboole_0(k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)),k3_xboole_0(k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)),X2))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_36]), c_0_43]), c_0_43]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 0.48/0.66  cnf(c_0_58, plain, (k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.48/0.66  cnf(c_0_59, plain, (k3_xboole_0(X1,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)))=X1), inference(spm,[status(thm)],[c_0_44, c_0_52])).
% 0.48/0.66  cnf(c_0_60, plain, (k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k5_xboole_0(X1,X1)))=k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.48/0.66  cnf(c_0_61, negated_conjecture, (k2_xboole_0(k1_tarski(esk5_0),esk6_0)!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.48/0.66  cnf(c_0_62, negated_conjecture, (r1_tarski(k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.48/0.66  cnf(c_0_63, plain, (k5_xboole_0(k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)),k3_xboole_0(k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)),k5_xboole_0(X2,k3_xboole_0(X2,X1))))=k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(spm,[status(thm)],[c_0_57, c_0_53])).
% 0.48/0.66  cnf(c_0_64, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_58]), c_0_58])).
% 0.48/0.66  cnf(c_0_65, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_59, c_0_58])).
% 0.48/0.66  cnf(c_0_66, plain, (k5_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_58]), c_0_58])).
% 0.48/0.66  cnf(c_0_67, negated_conjecture, (k3_tarski(k4_enumset1(k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0))!=esk6_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_47]), c_0_21]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39])).
% 0.48/0.66  cnf(c_0_68, negated_conjecture, (k3_xboole_0(k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)=k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_44, c_0_62])).
% 0.48/0.66  cnf(c_0_69, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_58]), c_0_58]), c_0_54]), c_0_65]), c_0_66])).
% 0.48/0.66  cnf(c_0_70, negated_conjecture, (k3_tarski(k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))!=esk6_0), inference(rw,[status(thm)],[c_0_67, c_0_51])).
% 0.48/0.66  cnf(c_0_71, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_68]), c_0_69]), c_0_51]), c_0_58]), c_0_70]), ['proof']).
% 0.48/0.66  # SZS output end CNFRefutation
% 0.48/0.66  # Proof object total steps             : 72
% 0.48/0.66  # Proof object clause steps            : 39
% 0.48/0.66  # Proof object formula steps           : 33
% 0.48/0.66  # Proof object conjectures             : 10
% 0.48/0.66  # Proof object clause conjectures      : 7
% 0.48/0.66  # Proof object formula conjectures     : 3
% 0.48/0.66  # Proof object initial clauses used    : 17
% 0.48/0.66  # Proof object initial formulas used   : 16
% 0.48/0.66  # Proof object generating inferences   : 12
% 0.48/0.66  # Proof object simplifying inferences  : 68
% 0.48/0.66  # Training examples: 0 positive, 0 negative
% 0.48/0.66  # Parsed axioms                        : 22
% 0.48/0.66  # Removed by relevancy pruning/SinE    : 0
% 0.48/0.66  # Initial clauses                      : 33
% 0.48/0.66  # Removed in clause preprocessing      : 7
% 0.48/0.66  # Initial clauses in saturation        : 26
% 0.48/0.66  # Processed clauses                    : 1872
% 0.48/0.66  # ...of these trivial                  : 114
% 0.48/0.66  # ...subsumed                          : 1215
% 0.48/0.66  # ...remaining for further processing  : 542
% 0.48/0.66  # Other redundant clauses eliminated   : 16
% 0.48/0.66  # Clauses deleted for lack of memory   : 0
% 0.48/0.66  # Backward-subsumed                    : 1
% 0.48/0.66  # Backward-rewritten                   : 25
% 0.48/0.66  # Generated clauses                    : 23121
% 0.48/0.66  # ...of the previous two non-trivial   : 15139
% 0.48/0.66  # Contextual simplify-reflections      : 0
% 0.48/0.66  # Paramodulations                      : 23103
% 0.48/0.66  # Factorizations                       : 2
% 0.48/0.66  # Equation resolutions                 : 16
% 0.48/0.66  # Propositional unsat checks           : 0
% 0.48/0.66  #    Propositional check models        : 0
% 0.48/0.66  #    Propositional check unsatisfiable : 0
% 0.48/0.66  #    Propositional clauses             : 0
% 0.48/0.66  #    Propositional clauses after purity: 0
% 0.48/0.66  #    Propositional unsat core size     : 0
% 0.48/0.66  #    Propositional preprocessing time  : 0.000
% 0.48/0.66  #    Propositional encoding time       : 0.000
% 0.48/0.66  #    Propositional solver time         : 0.000
% 0.48/0.66  #    Success case prop preproc time    : 0.000
% 0.48/0.66  #    Success case prop encoding time   : 0.000
% 0.48/0.66  #    Success case prop solver time     : 0.000
% 0.48/0.66  # Current number of processed clauses  : 489
% 0.48/0.66  #    Positive orientable unit clauses  : 118
% 0.48/0.66  #    Positive unorientable unit clauses: 1
% 0.48/0.66  #    Negative unit clauses             : 47
% 0.48/0.66  #    Non-unit-clauses                  : 323
% 0.48/0.66  # Current number of unprocessed clauses: 13260
% 0.48/0.66  # ...number of literals in the above   : 27503
% 0.48/0.66  # Current number of archived formulas  : 0
% 0.48/0.66  # Current number of archived clauses   : 58
% 0.48/0.66  # Clause-clause subsumption calls (NU) : 15758
% 0.48/0.66  # Rec. Clause-clause subsumption calls : 14493
% 0.48/0.66  # Non-unit clause-clause subsumptions  : 879
% 0.48/0.66  # Unit Clause-clause subsumption calls : 336
% 0.48/0.66  # Rewrite failures with RHS unbound    : 0
% 0.48/0.66  # BW rewrite match attempts            : 251
% 0.48/0.66  # BW rewrite match successes           : 37
% 0.48/0.66  # Condensation attempts                : 0
% 0.48/0.66  # Condensation successes               : 0
% 0.48/0.66  # Termbank termtop insertions          : 1578209
% 0.48/0.66  
% 0.48/0.66  # -------------------------------------------------
% 0.48/0.66  # User time                : 0.304 s
% 0.48/0.66  # System time              : 0.010 s
% 0.48/0.66  # Total time               : 0.314 s
% 0.48/0.66  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
