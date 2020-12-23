%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:38:49 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 632 expanded)
%              Number of clauses        :   44 ( 241 expanded)
%              Number of leaves         :   20 ( 194 expanded)
%              Depth                    :   12
%              Number of atoms          :  129 ( 739 expanded)
%              Number of equality atoms :   80 ( 596 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t26_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),k1_tarski(X3))
     => X1 = X3 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

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

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t12_zfmisc_1,axiom,(
    ! [X1,X2] : r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(t6_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),k1_tarski(X2))
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_20,plain,(
    ! [X25,X26] : r1_xboole_0(k4_xboole_0(X25,X26),X26) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_21,plain,(
    ! [X19,X20] : k4_xboole_0(X19,X20) = k5_xboole_0(X19,k3_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_22,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_24,plain,(
    ! [X10] : k3_xboole_0(X10,X10) = X10 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(k2_tarski(X1,X2),k1_tarski(X3))
       => X1 = X3 ) ),
    inference(assume_negation,[status(cth)],[t26_zfmisc_1])).

fof(c_0_26,plain,(
    ! [X23,X24] : r1_tarski(k4_xboole_0(X23,X24),X23) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_27,plain,(
    ! [X11,X12,X14,X15,X16] :
      ( ( r1_xboole_0(X11,X12)
        | r2_hidden(esk1_2(X11,X12),k3_xboole_0(X11,X12)) )
      & ( ~ r2_hidden(X16,k3_xboole_0(X14,X15))
        | ~ r1_xboole_0(X14,X15) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_28,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X55,X56] :
      ( ( ~ r1_tarski(X55,k1_tarski(X56))
        | X55 = k1_xboole_0
        | X55 = k1_tarski(X56) )
      & ( X55 != k1_xboole_0
        | r1_tarski(X55,k1_tarski(X56)) )
      & ( X55 != k1_tarski(X56)
        | r1_tarski(X55,k1_tarski(X56)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

fof(c_0_31,plain,(
    ! [X27] : k2_tarski(X27,X27) = k1_tarski(X27) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_32,plain,(
    ! [X28,X29] : k1_enumset1(X28,X28,X29) = k2_tarski(X28,X29) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_33,plain,(
    ! [X30,X31,X32] : k2_enumset1(X30,X30,X31,X32) = k1_enumset1(X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_34,plain,(
    ! [X33,X34,X35,X36] : k3_enumset1(X33,X33,X34,X35,X36) = k2_enumset1(X33,X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_35,plain,(
    ! [X37,X38,X39,X40,X41] : k4_enumset1(X37,X37,X38,X39,X40,X41) = k3_enumset1(X37,X38,X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_36,plain,(
    ! [X42,X43,X44,X45,X46,X47] : k5_enumset1(X42,X42,X43,X44,X45,X46,X47) = k4_enumset1(X42,X43,X44,X45,X46,X47) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_37,plain,(
    ! [X48,X49,X50,X51,X52,X53,X54] : k6_enumset1(X48,X48,X49,X50,X51,X52,X53,X54) = k5_enumset1(X48,X49,X50,X51,X52,X53,X54) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_38,negated_conjecture,
    ( r1_tarski(k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0))
    & esk3_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

fof(c_0_39,plain,(
    ! [X59,X60] :
      ( ( k4_xboole_0(k1_tarski(X59),k1_tarski(X60)) != k1_tarski(X59)
        | X59 != X60 )
      & ( X59 = X60
        | k4_xboole_0(k1_tarski(X59),k1_tarski(X60)) = k1_tarski(X59) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

cnf(c_0_40,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,plain,
    ( r1_xboole_0(k5_xboole_0(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_43,plain,(
    ! [X17] :
      ( X17 = k1_xboole_0
      | r2_hidden(esk2_1(X17),X17) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_44,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_45,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_48,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_49,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_50,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_51,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_53,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_54,plain,(
    ! [X21,X22] :
      ( ~ r1_tarski(X21,X22)
      | k3_xboole_0(X21,X22) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_55,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_40,c_0_23])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(k5_xboole_0(X2,X2),X2)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_57,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_58,plain,
    ( X1 = k1_xboole_0
    | X1 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_51]),c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_45]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_51]),c_0_51])).

fof(c_0_60,plain,(
    ! [X57,X58] : r1_tarski(k1_tarski(X57),k2_tarski(X57,X58)) ),
    inference(variable_rename,[status(thm)],[t12_zfmisc_1])).

cnf(c_0_61,plain,
    ( X1 != X2
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_45]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_46]),c_0_23]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_51]),c_0_51])).

cnf(c_0_62,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,plain,
    ( r1_tarski(k5_xboole_0(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_29])).

cnf(c_0_64,plain,
    ( k3_xboole_0(k5_xboole_0(X1,X1),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)
    | k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_66,plain,
    ( r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_67,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_61]),c_0_29])).

cnf(c_0_68,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

fof(c_0_69,plain,(
    ! [X61,X62] :
      ( ~ r1_tarski(k1_tarski(X61),k1_tarski(X62))
      | X61 = X62 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_zfmisc_1])])).

cnf(c_0_70,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) = k1_xboole_0
    | X1 = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)
    | X1 = k1_xboole_0
    | ~ r1_tarski(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_65])).

cnf(c_0_71,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_45]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_51]),c_0_51])).

cnf(c_0_72,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_73,plain,
    ( X1 = X2
    | ~ r1_tarski(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])).

fof(c_0_75,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_76,plain,
    ( X1 = X2
    | ~ r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_51]),c_0_51])).

cnf(c_0_77,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) = k1_xboole_0
    | r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( esk3_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_79,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_64,c_0_68])).

cnf(c_0_80,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_81,plain,
    ( k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_71])).

cnf(c_0_82,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])).

cnf(c_0_83,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83]),c_0_72]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:22:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.13/0.39  # and selection function GSelectMinInfpos.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.027 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.13/0.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.39  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.13/0.39  fof(t26_zfmisc_1, conjecture, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),k1_tarski(X3))=>X1=X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 0.13/0.39  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.13/0.39  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.13/0.39  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.13/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.39  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.13/0.39  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.13/0.39  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.13/0.39  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.13/0.39  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.13/0.39  fof(t12_zfmisc_1, axiom, ![X1, X2]:r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 0.13/0.39  fof(t6_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),k1_tarski(X2))=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 0.13/0.39  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.13/0.39  fof(c_0_20, plain, ![X25, X26]:r1_xboole_0(k4_xboole_0(X25,X26),X26), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.13/0.39  fof(c_0_21, plain, ![X19, X20]:k4_xboole_0(X19,X20)=k5_xboole_0(X19,k3_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.39  cnf(c_0_22, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.39  fof(c_0_24, plain, ![X10]:k3_xboole_0(X10,X10)=X10, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.13/0.39  fof(c_0_25, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),k1_tarski(X3))=>X1=X3)), inference(assume_negation,[status(cth)],[t26_zfmisc_1])).
% 0.13/0.39  fof(c_0_26, plain, ![X23, X24]:r1_tarski(k4_xboole_0(X23,X24),X23), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.13/0.39  fof(c_0_27, plain, ![X11, X12, X14, X15, X16]:((r1_xboole_0(X11,X12)|r2_hidden(esk1_2(X11,X12),k3_xboole_0(X11,X12)))&(~r2_hidden(X16,k3_xboole_0(X14,X15))|~r1_xboole_0(X14,X15))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.13/0.39  cnf(c_0_28, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.39  cnf(c_0_29, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  fof(c_0_30, plain, ![X55, X56]:((~r1_tarski(X55,k1_tarski(X56))|(X55=k1_xboole_0|X55=k1_tarski(X56)))&((X55!=k1_xboole_0|r1_tarski(X55,k1_tarski(X56)))&(X55!=k1_tarski(X56)|r1_tarski(X55,k1_tarski(X56))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.13/0.39  fof(c_0_31, plain, ![X27]:k2_tarski(X27,X27)=k1_tarski(X27), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.39  fof(c_0_32, plain, ![X28, X29]:k1_enumset1(X28,X28,X29)=k2_tarski(X28,X29), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.39  fof(c_0_33, plain, ![X30, X31, X32]:k2_enumset1(X30,X30,X31,X32)=k1_enumset1(X30,X31,X32), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.39  fof(c_0_34, plain, ![X33, X34, X35, X36]:k3_enumset1(X33,X33,X34,X35,X36)=k2_enumset1(X33,X34,X35,X36), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.39  fof(c_0_35, plain, ![X37, X38, X39, X40, X41]:k4_enumset1(X37,X37,X38,X39,X40,X41)=k3_enumset1(X37,X38,X39,X40,X41), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.39  fof(c_0_36, plain, ![X42, X43, X44, X45, X46, X47]:k5_enumset1(X42,X42,X43,X44,X45,X46,X47)=k4_enumset1(X42,X43,X44,X45,X46,X47), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.13/0.39  fof(c_0_37, plain, ![X48, X49, X50, X51, X52, X53, X54]:k6_enumset1(X48,X48,X49,X50,X51,X52,X53,X54)=k5_enumset1(X48,X49,X50,X51,X52,X53,X54), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.13/0.39  fof(c_0_38, negated_conjecture, (r1_tarski(k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0))&esk3_0!=esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.13/0.39  fof(c_0_39, plain, ![X59, X60]:((k4_xboole_0(k1_tarski(X59),k1_tarski(X60))!=k1_tarski(X59)|X59!=X60)&(X59=X60|k4_xboole_0(k1_tarski(X59),k1_tarski(X60))=k1_tarski(X59))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 0.13/0.39  cnf(c_0_40, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.39  cnf(c_0_41, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.39  cnf(c_0_42, plain, (r1_xboole_0(k5_xboole_0(X1,X1),X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.39  fof(c_0_43, plain, ![X17]:(X17=k1_xboole_0|r2_hidden(esk2_1(X17),X17)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.13/0.39  cnf(c_0_44, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.39  cnf(c_0_45, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.39  cnf(c_0_46, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.39  cnf(c_0_47, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.39  cnf(c_0_48, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.39  cnf(c_0_49, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.39  cnf(c_0_50, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.39  cnf(c_0_51, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.39  cnf(c_0_52, negated_conjecture, (r1_tarski(k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.39  cnf(c_0_53, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.39  fof(c_0_54, plain, ![X21, X22]:(~r1_tarski(X21,X22)|k3_xboole_0(X21,X22)=X21), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.13/0.39  cnf(c_0_55, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_40, c_0_23])).
% 0.13/0.39  cnf(c_0_56, plain, (~r2_hidden(X1,k3_xboole_0(k5_xboole_0(X2,X2),X2))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.39  cnf(c_0_57, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.39  cnf(c_0_58, plain, (X1=k1_xboole_0|X1=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|~r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_51]), c_0_51])).
% 0.13/0.39  cnf(c_0_59, negated_conjecture, (r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_45]), c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_51]), c_0_51])).
% 0.13/0.39  fof(c_0_60, plain, ![X57, X58]:r1_tarski(k1_tarski(X57),k2_tarski(X57,X58)), inference(variable_rename,[status(thm)],[t12_zfmisc_1])).
% 0.13/0.39  cnf(c_0_61, plain, (X1!=X2|k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))!=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_45]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_46]), c_0_23]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_51]), c_0_51])).
% 0.13/0.39  cnf(c_0_62, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.13/0.39  cnf(c_0_63, plain, (r1_tarski(k5_xboole_0(X1,X1),X1)), inference(spm,[status(thm)],[c_0_55, c_0_29])).
% 0.13/0.39  cnf(c_0_64, plain, (k3_xboole_0(k5_xboole_0(X1,X1),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.13/0.39  cnf(c_0_65, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)|k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.13/0.39  cnf(c_0_66, plain, (r1_tarski(k1_tarski(X1),k2_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.13/0.39  cnf(c_0_67, plain, (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))!=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_61]), c_0_29])).
% 0.13/0.39  cnf(c_0_68, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.13/0.39  fof(c_0_69, plain, ![X61, X62]:(~r1_tarski(k1_tarski(X61),k1_tarski(X62))|X61=X62), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_zfmisc_1])])).
% 0.13/0.39  cnf(c_0_70, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)=k1_xboole_0|X1=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)|X1=k1_xboole_0|~r1_tarski(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_58, c_0_65])).
% 0.13/0.39  cnf(c_0_71, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_45]), c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_51]), c_0_51])).
% 0.13/0.39  cnf(c_0_72, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_67, c_0_68])).
% 0.13/0.39  cnf(c_0_73, plain, (X1=X2|~r1_tarski(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.13/0.39  cnf(c_0_74, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72])).
% 0.13/0.39  fof(c_0_75, plain, ![X8, X9]:k3_xboole_0(X8,X9)=k3_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.13/0.39  cnf(c_0_76, plain, (X1=X2|~r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_51]), c_0_51])).
% 0.13/0.39  cnf(c_0_77, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)=k1_xboole_0|r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_59, c_0_74])).
% 0.13/0.39  cnf(c_0_78, negated_conjecture, (esk3_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.39  cnf(c_0_79, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_64, c_0_68])).
% 0.13/0.39  cnf(c_0_80, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.13/0.39  cnf(c_0_81, plain, (k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)), inference(spm,[status(thm)],[c_0_62, c_0_71])).
% 0.13/0.39  cnf(c_0_82, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78])).
% 0.13/0.39  cnf(c_0_83, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.13/0.39  cnf(c_0_84, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_83]), c_0_72]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 85
% 0.13/0.39  # Proof object clause steps            : 44
% 0.13/0.39  # Proof object formula steps           : 41
% 0.13/0.39  # Proof object conjectures             : 12
% 0.13/0.39  # Proof object clause conjectures      : 9
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 21
% 0.13/0.39  # Proof object initial formulas used   : 20
% 0.13/0.39  # Proof object generating inferences   : 13
% 0.13/0.39  # Proof object simplifying inferences  : 92
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 20
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 25
% 0.13/0.39  # Removed in clause preprocessing      : 8
% 0.13/0.39  # Initial clauses in saturation        : 17
% 0.13/0.39  # Processed clauses                    : 216
% 0.13/0.39  # ...of these trivial                  : 15
% 0.13/0.39  # ...subsumed                          : 101
% 0.13/0.39  # ...remaining for further processing  : 100
% 0.13/0.39  # Other redundant clauses eliminated   : 3
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 0
% 0.13/0.39  # Backward-rewritten                   : 31
% 0.13/0.39  # Generated clauses                    : 552
% 0.13/0.39  # ...of the previous two non-trivial   : 410
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 548
% 0.13/0.39  # Factorizations                       : 1
% 0.13/0.39  # Equation resolutions                 : 3
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 50
% 0.13/0.39  #    Positive orientable unit clauses  : 28
% 0.13/0.39  #    Positive unorientable unit clauses: 1
% 0.13/0.39  #    Negative unit clauses             : 11
% 0.13/0.39  #    Non-unit-clauses                  : 10
% 0.13/0.39  # Current number of unprocessed clauses: 217
% 0.13/0.39  # ...number of literals in the above   : 294
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 55
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 38
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 35
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 6
% 0.13/0.39  # Unit Clause-clause subsumption calls : 27
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 57
% 0.13/0.39  # BW rewrite match successes           : 28
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 11527
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.037 s
% 0.13/0.39  # System time              : 0.004 s
% 0.13/0.39  # Total time               : 0.042 s
% 0.13/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
