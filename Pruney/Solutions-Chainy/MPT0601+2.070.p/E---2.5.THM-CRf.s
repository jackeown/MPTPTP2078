%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:21 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 400 expanded)
%              Number of clauses        :   42 ( 146 expanded)
%              Number of leaves         :   20 ( 122 expanded)
%              Depth                    :    9
%              Number of atoms          :  160 ( 582 expanded)
%              Number of equality atoms :   64 ( 372 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t205_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t20_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k2_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

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

fof(t19_zfmisc_1,axiom,(
    ! [X1,X2] : k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k1_relat_1(X2))
        <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t205_relat_1])).

fof(c_0_21,plain,(
    ! [X50,X51,X52,X54] :
      ( ( r2_hidden(esk2_3(X50,X51,X52),k2_relat_1(X52))
        | ~ r2_hidden(X50,k10_relat_1(X52,X51))
        | ~ v1_relat_1(X52) )
      & ( r2_hidden(k4_tarski(X50,esk2_3(X50,X51,X52)),X52)
        | ~ r2_hidden(X50,k10_relat_1(X52,X51))
        | ~ v1_relat_1(X52) )
      & ( r2_hidden(esk2_3(X50,X51,X52),X51)
        | ~ r2_hidden(X50,k10_relat_1(X52,X51))
        | ~ v1_relat_1(X52) )
      & ( ~ r2_hidden(X54,k2_relat_1(X52))
        | ~ r2_hidden(k4_tarski(X50,X54),X52)
        | ~ r2_hidden(X54,X51)
        | r2_hidden(X50,k10_relat_1(X52,X51))
        | ~ v1_relat_1(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

fof(c_0_22,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & ( ~ r2_hidden(esk3_0,k1_relat_1(esk4_0))
      | k11_relat_1(esk4_0,esk3_0) = k1_xboole_0 )
    & ( r2_hidden(esk3_0,k1_relat_1(esk4_0))
      | k11_relat_1(esk4_0,esk3_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_23,plain,(
    ! [X55] :
      ( ~ v1_relat_1(X55)
      | k10_relat_1(X55,k2_relat_1(X55)) = k1_relat_1(X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

fof(c_0_24,plain,(
    ! [X56,X57,X58] :
      ( ( ~ r2_hidden(k4_tarski(X56,X57),X58)
        | r2_hidden(X57,k11_relat_1(X58,X56))
        | ~ v1_relat_1(X58) )
      & ( ~ r2_hidden(X57,k11_relat_1(X58,X56))
        | r2_hidden(k4_tarski(X56,X57),X58)
        | ~ v1_relat_1(X58) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

fof(c_0_25,plain,(
    ! [X8] :
      ( X8 = k1_xboole_0
      | r2_hidden(esk1_1(X8),X8) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_26,plain,(
    ! [X59,X60,X61] :
      ( ( r2_hidden(X59,k1_relat_1(X61))
        | ~ r2_hidden(k4_tarski(X59,X60),X61)
        | ~ v1_relat_1(X61) )
      & ( r2_hidden(X60,k2_relat_1(X61))
        | ~ r2_hidden(k4_tarski(X59,X60),X61)
        | ~ v1_relat_1(X61) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X1,X2,X3)),X3)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,k11_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(esk4_0))
    | k11_relat_1(esk4_0,esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_34,plain,(
    ! [X48,X49] : k1_setfam_1(k2_tarski(X48,X49)) = k3_xboole_0(X48,X49) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_35,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_3(X1,X2,esk4_0)),esk4_0)
    | ~ r2_hidden(X1,k10_relat_1(esk4_0,X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( k10_relat_1(esk4_0,k2_relat_1(esk4_0)) = k1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk4_0)
    | ~ r2_hidden(X2,k11_relat_1(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk1_1(k11_relat_1(esk4_0,esk3_0)),k11_relat_1(esk4_0,esk3_0))
    | r2_hidden(esk3_0,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk4_0))
    | ~ r2_hidden(k4_tarski(X1,X2),esk4_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_28])).

fof(c_0_41,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_42,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_44,plain,(
    ! [X42,X43] :
      ( ( ~ r1_tarski(k1_tarski(X42),X43)
        | r2_hidden(X42,X43) )
      & ( ~ r2_hidden(X42,X43)
        | r1_tarski(k1_tarski(X42),X43) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_45,plain,(
    ! [X14] : k2_tarski(X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_46,plain,(
    ! [X17,X18,X19] : k2_enumset1(X17,X17,X18,X19) = k1_enumset1(X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_47,plain,(
    ! [X20,X21,X22,X23] : k3_enumset1(X20,X20,X21,X22,X23) = k2_enumset1(X20,X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_48,plain,(
    ! [X24,X25,X26,X27,X28] : k4_enumset1(X24,X24,X25,X26,X27,X28) = k3_enumset1(X24,X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_49,plain,(
    ! [X29,X30,X31,X32,X33,X34] : k5_enumset1(X29,X29,X30,X31,X32,X33,X34) = k4_enumset1(X29,X30,X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_50,plain,(
    ! [X35,X36,X37,X38,X39,X40,X41] : k6_enumset1(X35,X35,X36,X37,X38,X39,X40,X41) = k5_enumset1(X35,X36,X37,X38,X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_51,plain,
    ( r2_hidden(X2,k11_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_3(X1,k2_relat_1(esk4_0),esk4_0)),esk4_0)
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_54,negated_conjecture,
    ( k11_relat_1(esk4_0,esk3_0) = k1_xboole_0
    | ~ r2_hidden(esk3_0,k1_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_55,plain,(
    ! [X46,X47] :
      ( ( k4_xboole_0(k1_tarski(X46),k1_tarski(X47)) != k1_tarski(X46)
        | X46 != X47 )
      & ( X46 = X47
        | k4_xboole_0(k1_tarski(X46),k1_tarski(X47)) = k1_tarski(X46) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_57,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_58,plain,(
    ! [X44,X45] : k3_xboole_0(k1_tarski(X44),k2_tarski(X44,X45)) = k1_tarski(X44) ),
    inference(variable_rename,[status(thm)],[t19_zfmisc_1])).

cnf(c_0_59,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_60,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_61,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_62,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_63,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_64,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_65,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(X1,k11_relat_1(esk4_0,X2))
    | ~ r2_hidden(k4_tarski(X2,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_28])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_68,negated_conjecture,
    ( k11_relat_1(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_53])])).

cnf(c_0_69,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_70,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_71,plain,
    ( k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_72,plain,(
    ! [X13] : k5_xboole_0(X13,X13) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_73,plain,(
    ! [X12] :
      ( ~ r1_tarski(X12,k1_xboole_0)
      | X12 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_74,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60]),c_0_43]),c_0_61]),c_0_62]),c_0_63]),c_0_64]),c_0_65])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])).

cnf(c_0_76,plain,
    ( X1 != X2
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_60]),c_0_60]),c_0_60]),c_0_43]),c_0_43]),c_0_43]),c_0_70]),c_0_61]),c_0_61]),c_0_61]),c_0_61]),c_0_61]),c_0_61]),c_0_62]),c_0_62]),c_0_62]),c_0_62]),c_0_62]),c_0_62]),c_0_62]),c_0_63]),c_0_63]),c_0_63]),c_0_63]),c_0_63]),c_0_63]),c_0_63]),c_0_63]),c_0_64]),c_0_64]),c_0_64]),c_0_64]),c_0_64]),c_0_64]),c_0_64]),c_0_64]),c_0_64]),c_0_65]),c_0_65]),c_0_65]),c_0_65]),c_0_65]),c_0_65]),c_0_65]),c_0_65]),c_0_65]),c_0_65])).

cnf(c_0_77,plain,
    ( k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_60]),c_0_60]),c_0_43]),c_0_43]),c_0_43]),c_0_57]),c_0_61]),c_0_61]),c_0_61]),c_0_61]),c_0_61]),c_0_62]),c_0_62]),c_0_62]),c_0_62]),c_0_62]),c_0_62]),c_0_63]),c_0_63]),c_0_63]),c_0_63]),c_0_63]),c_0_63]),c_0_63]),c_0_64]),c_0_64]),c_0_64]),c_0_64]),c_0_64]),c_0_64]),c_0_64]),c_0_64]),c_0_65]),c_0_65]),c_0_65]),c_0_65]),c_0_65]),c_0_65]),c_0_65]),c_0_65]),c_0_65])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_79,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0),esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0),esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0),esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0),esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0),esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0),esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0),esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_81,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_76]),c_0_77]),c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:43:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 2.24/2.47  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 2.24/2.47  # and selection function SelectNegativeLiterals.
% 2.24/2.47  #
% 2.24/2.47  # Preprocessing time       : 0.028 s
% 2.24/2.47  # Presaturation interreduction done
% 2.24/2.47  
% 2.24/2.47  # Proof found!
% 2.24/2.47  # SZS status Theorem
% 2.24/2.47  # SZS output start CNFRefutation
% 2.24/2.47  fof(t205_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 2.24/2.47  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.24/2.47  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.24/2.47  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 2.24/2.47  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.24/2.47  fof(t20_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k2_relat_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 2.24/2.47  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.24/2.47  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.24/2.47  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.24/2.47  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.24/2.47  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.24/2.47  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.24/2.47  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.24/2.47  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.24/2.47  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 2.24/2.47  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 2.24/2.47  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.24/2.47  fof(t19_zfmisc_1, axiom, ![X1, X2]:k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 2.24/2.47  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.24/2.47  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.24/2.47  fof(c_0_20, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t205_relat_1])).
% 2.24/2.47  fof(c_0_21, plain, ![X50, X51, X52, X54]:((((r2_hidden(esk2_3(X50,X51,X52),k2_relat_1(X52))|~r2_hidden(X50,k10_relat_1(X52,X51))|~v1_relat_1(X52))&(r2_hidden(k4_tarski(X50,esk2_3(X50,X51,X52)),X52)|~r2_hidden(X50,k10_relat_1(X52,X51))|~v1_relat_1(X52)))&(r2_hidden(esk2_3(X50,X51,X52),X51)|~r2_hidden(X50,k10_relat_1(X52,X51))|~v1_relat_1(X52)))&(~r2_hidden(X54,k2_relat_1(X52))|~r2_hidden(k4_tarski(X50,X54),X52)|~r2_hidden(X54,X51)|r2_hidden(X50,k10_relat_1(X52,X51))|~v1_relat_1(X52))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 2.24/2.47  fof(c_0_22, negated_conjecture, (v1_relat_1(esk4_0)&((~r2_hidden(esk3_0,k1_relat_1(esk4_0))|k11_relat_1(esk4_0,esk3_0)=k1_xboole_0)&(r2_hidden(esk3_0,k1_relat_1(esk4_0))|k11_relat_1(esk4_0,esk3_0)!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 2.24/2.47  fof(c_0_23, plain, ![X55]:(~v1_relat_1(X55)|k10_relat_1(X55,k2_relat_1(X55))=k1_relat_1(X55)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 2.24/2.47  fof(c_0_24, plain, ![X56, X57, X58]:((~r2_hidden(k4_tarski(X56,X57),X58)|r2_hidden(X57,k11_relat_1(X58,X56))|~v1_relat_1(X58))&(~r2_hidden(X57,k11_relat_1(X58,X56))|r2_hidden(k4_tarski(X56,X57),X58)|~v1_relat_1(X58))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 2.24/2.47  fof(c_0_25, plain, ![X8]:(X8=k1_xboole_0|r2_hidden(esk1_1(X8),X8)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 2.24/2.47  fof(c_0_26, plain, ![X59, X60, X61]:((r2_hidden(X59,k1_relat_1(X61))|~r2_hidden(k4_tarski(X59,X60),X61)|~v1_relat_1(X61))&(r2_hidden(X60,k2_relat_1(X61))|~r2_hidden(k4_tarski(X59,X60),X61)|~v1_relat_1(X61))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).
% 2.24/2.47  cnf(c_0_27, plain, (r2_hidden(k4_tarski(X1,esk2_3(X1,X2,X3)),X3)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.24/2.47  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.24/2.47  cnf(c_0_29, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.24/2.47  cnf(c_0_30, plain, (r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,k11_relat_1(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.24/2.47  cnf(c_0_31, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(esk4_0))|k11_relat_1(esk4_0,esk3_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.24/2.47  cnf(c_0_32, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 2.24/2.47  cnf(c_0_33, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.24/2.47  fof(c_0_34, plain, ![X48, X49]:k1_setfam_1(k2_tarski(X48,X49))=k3_xboole_0(X48,X49), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 2.24/2.47  fof(c_0_35, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 2.24/2.47  cnf(c_0_36, negated_conjecture, (r2_hidden(k4_tarski(X1,esk2_3(X1,X2,esk4_0)),esk4_0)|~r2_hidden(X1,k10_relat_1(esk4_0,X2))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 2.24/2.47  cnf(c_0_37, negated_conjecture, (k10_relat_1(esk4_0,k2_relat_1(esk4_0))=k1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_29, c_0_28])).
% 2.24/2.47  cnf(c_0_38, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),esk4_0)|~r2_hidden(X2,k11_relat_1(esk4_0,X1))), inference(spm,[status(thm)],[c_0_30, c_0_28])).
% 2.24/2.47  cnf(c_0_39, negated_conjecture, (r2_hidden(esk1_1(k11_relat_1(esk4_0,esk3_0)),k11_relat_1(esk4_0,esk3_0))|r2_hidden(esk3_0,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 2.24/2.47  cnf(c_0_40, negated_conjecture, (r2_hidden(X1,k1_relat_1(esk4_0))|~r2_hidden(k4_tarski(X1,X2),esk4_0)), inference(spm,[status(thm)],[c_0_33, c_0_28])).
% 2.24/2.47  fof(c_0_41, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 2.24/2.47  cnf(c_0_42, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 2.24/2.47  cnf(c_0_43, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 2.24/2.47  fof(c_0_44, plain, ![X42, X43]:((~r1_tarski(k1_tarski(X42),X43)|r2_hidden(X42,X43))&(~r2_hidden(X42,X43)|r1_tarski(k1_tarski(X42),X43))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 2.24/2.47  fof(c_0_45, plain, ![X14]:k2_tarski(X14,X14)=k1_tarski(X14), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 2.24/2.47  fof(c_0_46, plain, ![X17, X18, X19]:k2_enumset1(X17,X17,X18,X19)=k1_enumset1(X17,X18,X19), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 2.24/2.47  fof(c_0_47, plain, ![X20, X21, X22, X23]:k3_enumset1(X20,X20,X21,X22,X23)=k2_enumset1(X20,X21,X22,X23), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 2.24/2.47  fof(c_0_48, plain, ![X24, X25, X26, X27, X28]:k4_enumset1(X24,X24,X25,X26,X27,X28)=k3_enumset1(X24,X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 2.24/2.47  fof(c_0_49, plain, ![X29, X30, X31, X32, X33, X34]:k5_enumset1(X29,X29,X30,X31,X32,X33,X34)=k4_enumset1(X29,X30,X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 2.24/2.47  fof(c_0_50, plain, ![X35, X36, X37, X38, X39, X40, X41]:k6_enumset1(X35,X35,X36,X37,X38,X39,X40,X41)=k5_enumset1(X35,X36,X37,X38,X39,X40,X41), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 2.24/2.47  cnf(c_0_51, plain, (r2_hidden(X2,k11_relat_1(X3,X1))|~r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.24/2.47  cnf(c_0_52, negated_conjecture, (r2_hidden(k4_tarski(X1,esk2_3(X1,k2_relat_1(esk4_0),esk4_0)),esk4_0)|~r2_hidden(X1,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 2.24/2.47  cnf(c_0_53, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 2.24/2.47  cnf(c_0_54, negated_conjecture, (k11_relat_1(esk4_0,esk3_0)=k1_xboole_0|~r2_hidden(esk3_0,k1_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.24/2.47  fof(c_0_55, plain, ![X46, X47]:((k4_xboole_0(k1_tarski(X46),k1_tarski(X47))!=k1_tarski(X46)|X46!=X47)&(X46=X47|k4_xboole_0(k1_tarski(X46),k1_tarski(X47))=k1_tarski(X46))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 2.24/2.47  cnf(c_0_56, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 2.24/2.47  cnf(c_0_57, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 2.24/2.47  fof(c_0_58, plain, ![X44, X45]:k3_xboole_0(k1_tarski(X44),k2_tarski(X44,X45))=k1_tarski(X44), inference(variable_rename,[status(thm)],[t19_zfmisc_1])).
% 2.24/2.47  cnf(c_0_59, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 2.24/2.47  cnf(c_0_60, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 2.24/2.47  cnf(c_0_61, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 2.24/2.47  cnf(c_0_62, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 2.24/2.47  cnf(c_0_63, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 2.24/2.47  cnf(c_0_64, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 2.24/2.47  cnf(c_0_65, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 2.24/2.47  cnf(c_0_66, negated_conjecture, (r2_hidden(X1,k11_relat_1(esk4_0,X2))|~r2_hidden(k4_tarski(X2,X1),esk4_0)), inference(spm,[status(thm)],[c_0_51, c_0_28])).
% 2.24/2.47  cnf(c_0_67, negated_conjecture, (r2_hidden(k4_tarski(esk3_0,esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0)),esk4_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 2.24/2.47  cnf(c_0_68, negated_conjecture, (k11_relat_1(esk4_0,esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_53])])).
% 2.24/2.47  cnf(c_0_69, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_55])).
% 2.24/2.47  cnf(c_0_70, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_56, c_0_57])).
% 2.24/2.47  cnf(c_0_71, plain, (k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 2.24/2.47  fof(c_0_72, plain, ![X13]:k5_xboole_0(X13,X13)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 2.24/2.47  fof(c_0_73, plain, ![X12]:(~r1_tarski(X12,k1_xboole_0)|X12=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 2.24/2.47  cnf(c_0_74, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60]), c_0_43]), c_0_61]), c_0_62]), c_0_63]), c_0_64]), c_0_65])).
% 2.24/2.47  cnf(c_0_75, negated_conjecture, (r2_hidden(esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0),k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])).
% 2.24/2.47  cnf(c_0_76, plain, (X1!=X2|k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))!=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_60]), c_0_60]), c_0_60]), c_0_43]), c_0_43]), c_0_43]), c_0_70]), c_0_61]), c_0_61]), c_0_61]), c_0_61]), c_0_61]), c_0_61]), c_0_62]), c_0_62]), c_0_62]), c_0_62]), c_0_62]), c_0_62]), c_0_62]), c_0_63]), c_0_63]), c_0_63]), c_0_63]), c_0_63]), c_0_63]), c_0_63]), c_0_63]), c_0_64]), c_0_64]), c_0_64]), c_0_64]), c_0_64]), c_0_64]), c_0_64]), c_0_64]), c_0_64]), c_0_65]), c_0_65]), c_0_65]), c_0_65]), c_0_65]), c_0_65]), c_0_65]), c_0_65]), c_0_65]), c_0_65])).
% 2.24/2.47  cnf(c_0_77, plain, (k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_60]), c_0_60]), c_0_43]), c_0_43]), c_0_43]), c_0_57]), c_0_61]), c_0_61]), c_0_61]), c_0_61]), c_0_61]), c_0_62]), c_0_62]), c_0_62]), c_0_62]), c_0_62]), c_0_62]), c_0_63]), c_0_63]), c_0_63]), c_0_63]), c_0_63]), c_0_63]), c_0_63]), c_0_64]), c_0_64]), c_0_64]), c_0_64]), c_0_64]), c_0_64]), c_0_64]), c_0_64]), c_0_65]), c_0_65]), c_0_65]), c_0_65]), c_0_65]), c_0_65]), c_0_65]), c_0_65]), c_0_65])).
% 2.24/2.47  cnf(c_0_78, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_72])).
% 2.24/2.47  cnf(c_0_79, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 2.24/2.47  cnf(c_0_80, negated_conjecture, (r1_tarski(k6_enumset1(esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0),esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0),esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0),esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0),esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0),esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0),esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0),esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 2.24/2.47  cnf(c_0_81, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_76]), c_0_77]), c_0_78])).
% 2.24/2.47  cnf(c_0_82, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81]), ['proof']).
% 2.24/2.47  # SZS output end CNFRefutation
% 2.24/2.47  # Proof object total steps             : 83
% 2.24/2.47  # Proof object clause steps            : 42
% 2.24/2.47  # Proof object formula steps           : 41
% 2.24/2.47  # Proof object conjectures             : 19
% 2.24/2.47  # Proof object clause conjectures      : 16
% 2.24/2.47  # Proof object formula conjectures     : 3
% 2.24/2.47  # Proof object initial clauses used    : 23
% 2.24/2.47  # Proof object initial formulas used   : 20
% 2.24/2.47  # Proof object generating inferences   : 12
% 2.24/2.47  # Proof object simplifying inferences  : 105
% 2.24/2.47  # Training examples: 0 positive, 0 negative
% 2.24/2.47  # Parsed axioms                        : 20
% 2.24/2.47  # Removed by relevancy pruning/SinE    : 0
% 2.24/2.47  # Initial clauses                      : 29
% 2.24/2.47  # Removed in clause preprocessing      : 9
% 2.24/2.47  # Initial clauses in saturation        : 20
% 2.24/2.47  # Processed clauses                    : 6353
% 2.24/2.47  # ...of these trivial                  : 65
% 2.24/2.47  # ...subsumed                          : 4778
% 2.24/2.47  # ...remaining for further processing  : 1510
% 2.24/2.47  # Other redundant clauses eliminated   : 39
% 2.24/2.47  # Clauses deleted for lack of memory   : 0
% 2.24/2.47  # Backward-subsumed                    : 247
% 2.24/2.47  # Backward-rewritten                   : 264
% 2.24/2.47  # Generated clauses                    : 141937
% 2.24/2.47  # ...of the previous two non-trivial   : 135054
% 2.24/2.47  # Contextual simplify-reflections      : 5
% 2.24/2.47  # Paramodulations                      : 141794
% 2.24/2.47  # Factorizations                       : 104
% 2.24/2.47  # Equation resolutions                 : 39
% 2.24/2.47  # Propositional unsat checks           : 0
% 2.24/2.47  #    Propositional check models        : 0
% 2.24/2.47  #    Propositional check unsatisfiable : 0
% 2.24/2.47  #    Propositional clauses             : 0
% 2.24/2.47  #    Propositional clauses after purity: 0
% 2.24/2.47  #    Propositional unsat core size     : 0
% 2.24/2.47  #    Propositional preprocessing time  : 0.000
% 2.24/2.47  #    Propositional encoding time       : 0.000
% 2.24/2.47  #    Propositional solver time         : 0.000
% 2.24/2.47  #    Success case prop preproc time    : 0.000
% 2.24/2.47  #    Success case prop encoding time   : 0.000
% 2.24/2.47  #    Success case prop solver time     : 0.000
% 2.24/2.47  # Current number of processed clauses  : 978
% 2.24/2.47  #    Positive orientable unit clauses  : 40
% 2.24/2.47  #    Positive unorientable unit clauses: 0
% 2.24/2.47  #    Negative unit clauses             : 1
% 2.24/2.47  #    Non-unit-clauses                  : 937
% 2.24/2.47  # Current number of unprocessed clauses: 127890
% 2.24/2.47  # ...number of literals in the above   : 681786
% 2.24/2.47  # Current number of archived formulas  : 0
% 2.24/2.47  # Current number of archived clauses   : 540
% 2.24/2.47  # Clause-clause subsumption calls (NU) : 194026
% 2.24/2.47  # Rec. Clause-clause subsumption calls : 36092
% 2.24/2.47  # Non-unit clause-clause subsumptions  : 5021
% 2.24/2.47  # Unit Clause-clause subsumption calls : 2601
% 2.24/2.47  # Rewrite failures with RHS unbound    : 0
% 2.24/2.47  # BW rewrite match attempts            : 438
% 2.24/2.47  # BW rewrite match successes           : 49
% 2.24/2.47  # Condensation attempts                : 0
% 2.24/2.47  # Condensation successes               : 0
% 2.24/2.47  # Termbank termtop insertions          : 9288551
% 2.24/2.48  
% 2.24/2.48  # -------------------------------------------------
% 2.24/2.48  # User time                : 2.074 s
% 2.24/2.48  # System time              : 0.059 s
% 2.24/2.48  # Total time               : 2.133 s
% 2.24/2.48  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
