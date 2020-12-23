%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:21 EST 2020

% Result     : Theorem 24.16s
% Output     : CNFRefutation 24.16s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 258 expanded)
%              Number of clauses        :   41 (  98 expanded)
%              Number of leaves         :   19 (  75 expanded)
%              Depth                    :    9
%              Number of atoms          :  157 ( 440 expanded)
%              Number of equality atoms :   61 ( 230 expanded)
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

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(t11_setfam_1,axiom,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k1_relat_1(X2))
        <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t205_relat_1])).

fof(c_0_20,plain,(
    ! [X41,X42,X43,X45] :
      ( ( r2_hidden(esk2_3(X41,X42,X43),k2_relat_1(X43))
        | ~ r2_hidden(X41,k10_relat_1(X43,X42))
        | ~ v1_relat_1(X43) )
      & ( r2_hidden(k4_tarski(X41,esk2_3(X41,X42,X43)),X43)
        | ~ r2_hidden(X41,k10_relat_1(X43,X42))
        | ~ v1_relat_1(X43) )
      & ( r2_hidden(esk2_3(X41,X42,X43),X42)
        | ~ r2_hidden(X41,k10_relat_1(X43,X42))
        | ~ v1_relat_1(X43) )
      & ( ~ r2_hidden(X45,k2_relat_1(X43))
        | ~ r2_hidden(k4_tarski(X41,X45),X43)
        | ~ r2_hidden(X45,X42)
        | r2_hidden(X41,k10_relat_1(X43,X42))
        | ~ v1_relat_1(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

fof(c_0_21,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & ( ~ r2_hidden(esk3_0,k1_relat_1(esk4_0))
      | k11_relat_1(esk4_0,esk3_0) = k1_xboole_0 )
    & ( r2_hidden(esk3_0,k1_relat_1(esk4_0))
      | k11_relat_1(esk4_0,esk3_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_22,plain,(
    ! [X46] :
      ( ~ v1_relat_1(X46)
      | k10_relat_1(X46,k2_relat_1(X46)) = k1_relat_1(X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

fof(c_0_23,plain,(
    ! [X47,X48,X49] :
      ( ( ~ r2_hidden(k4_tarski(X47,X48),X49)
        | r2_hidden(X48,k11_relat_1(X49,X47))
        | ~ v1_relat_1(X49) )
      & ( ~ r2_hidden(X48,k11_relat_1(X49,X47))
        | r2_hidden(k4_tarski(X47,X48),X49)
        | ~ v1_relat_1(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

fof(c_0_24,plain,(
    ! [X7] :
      ( X7 = k1_xboole_0
      | r2_hidden(esk1_1(X7),X7) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_25,plain,(
    ! [X50,X51,X52] :
      ( ( r2_hidden(X50,k1_relat_1(X52))
        | ~ r2_hidden(k4_tarski(X50,X51),X52)
        | ~ v1_relat_1(X52) )
      & ( r2_hidden(X51,k2_relat_1(X52))
        | ~ r2_hidden(k4_tarski(X50,X51),X52)
        | ~ v1_relat_1(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X1,X2,X3)),X3)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,k11_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(esk4_0))
    | k11_relat_1(esk4_0,esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_33,plain,(
    ! [X39,X40] : k1_setfam_1(k2_tarski(X39,X40)) = k3_xboole_0(X39,X40) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_34,plain,(
    ! [X14,X15] : k1_enumset1(X14,X14,X15) = k2_tarski(X14,X15) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_3(X1,X2,esk4_0)),esk4_0)
    | ~ r2_hidden(X1,k10_relat_1(esk4_0,X2)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( k10_relat_1(esk4_0,k2_relat_1(esk4_0)) = k1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk4_0)
    | ~ r2_hidden(X2,k11_relat_1(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk1_1(k11_relat_1(esk4_0,esk3_0)),k11_relat_1(esk4_0,esk3_0))
    | r2_hidden(esk3_0,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk4_0))
    | ~ r2_hidden(k4_tarski(X1,X2),esk4_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_27])).

fof(c_0_40,plain,(
    ! [X9,X10] : k4_xboole_0(X9,X10) = k5_xboole_0(X9,k3_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_41,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_43,plain,(
    ! [X34,X35] :
      ( ( ~ r1_tarski(k1_tarski(X34),X35)
        | r2_hidden(X34,X35) )
      & ( ~ r2_hidden(X34,X35)
        | r1_tarski(k1_tarski(X34),X35) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_44,plain,(
    ! [X13] : k2_tarski(X13,X13) = k1_tarski(X13) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_45,plain,(
    ! [X16,X17,X18] : k2_enumset1(X16,X16,X17,X18) = k1_enumset1(X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_46,plain,(
    ! [X19,X20,X21,X22] : k3_enumset1(X19,X19,X20,X21,X22) = k2_enumset1(X19,X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_47,plain,(
    ! [X23,X24,X25,X26,X27] : k4_enumset1(X23,X23,X24,X25,X26,X27) = k3_enumset1(X23,X24,X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_48,plain,(
    ! [X28,X29,X30,X31,X32,X33] : k5_enumset1(X28,X28,X29,X30,X31,X32,X33) = k4_enumset1(X28,X29,X30,X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

cnf(c_0_49,plain,
    ( r2_hidden(X2,k11_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_3(X1,k2_relat_1(esk4_0),esk4_0)),esk4_0)
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_52,negated_conjecture,
    ( k11_relat_1(esk4_0,esk3_0) = k1_xboole_0
    | ~ r2_hidden(esk3_0,k1_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_53,plain,(
    ! [X36,X37] :
      ( ( k4_xboole_0(k1_tarski(X36),k1_tarski(X37)) != k1_tarski(X36)
        | X36 != X37 )
      & ( X36 = X37
        | k4_xboole_0(k1_tarski(X36),k1_tarski(X37)) = k1_tarski(X36) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_55,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_56,plain,(
    ! [X38] : k1_setfam_1(k1_tarski(X38)) = X38 ),
    inference(variable_rename,[status(thm)],[t11_setfam_1])).

cnf(c_0_57,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_58,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_59,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_60,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_61,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_62,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(X1,k11_relat_1(esk4_0,X2))
    | ~ r2_hidden(k4_tarski(X2,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_27])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_65,negated_conjecture,
    ( k11_relat_1(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_51])])).

cnf(c_0_66,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_67,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_68,plain,
    ( k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_69,plain,(
    ! [X12] : k5_xboole_0(X12,X12) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_70,plain,(
    ! [X11] :
      ( ~ r1_tarski(X11,k1_xboole_0)
      | X11 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_71,plain,
    ( r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58]),c_0_42]),c_0_59]),c_0_60]),c_0_61]),c_0_62])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_73,plain,
    ( X1 != X2
    | k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2)))) != k5_enumset1(X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_58]),c_0_58]),c_0_58]),c_0_42]),c_0_42]),c_0_42]),c_0_67]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_60]),c_0_60]),c_0_60]),c_0_60]),c_0_60]),c_0_60]),c_0_60]),c_0_61]),c_0_61]),c_0_61]),c_0_61]),c_0_61]),c_0_61]),c_0_61]),c_0_61]),c_0_62]),c_0_62]),c_0_62]),c_0_62]),c_0_62]),c_0_62]),c_0_62]),c_0_62]),c_0_62])).

cnf(c_0_74,plain,
    ( k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_58]),c_0_42]),c_0_59]),c_0_60]),c_0_61]),c_0_62])).

cnf(c_0_75,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_76,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(k5_enumset1(esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0),esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0),esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0),esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0),esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0),esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0),esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_78,plain,
    ( k5_enumset1(X1,X1,X1,X1,X1,X1,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_73]),c_0_74]),c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:37:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 24.16/24.40  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 24.16/24.40  # and selection function SelectNegativeLiterals.
% 24.16/24.40  #
% 24.16/24.40  # Preprocessing time       : 0.027 s
% 24.16/24.40  # Presaturation interreduction done
% 24.16/24.40  
% 24.16/24.40  # Proof found!
% 24.16/24.40  # SZS status Theorem
% 24.16/24.40  # SZS output start CNFRefutation
% 24.16/24.40  fof(t205_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 24.16/24.40  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 24.16/24.40  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 24.16/24.40  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 24.16/24.40  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 24.16/24.40  fof(t20_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k2_relat_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 24.16/24.40  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 24.16/24.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 24.16/24.40  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 24.16/24.40  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 24.16/24.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 24.16/24.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 24.16/24.40  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 24.16/24.40  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 24.16/24.40  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 24.16/24.40  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 24.16/24.40  fof(t11_setfam_1, axiom, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 24.16/24.40  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 24.16/24.40  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 24.16/24.40  fof(c_0_19, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t205_relat_1])).
% 24.16/24.40  fof(c_0_20, plain, ![X41, X42, X43, X45]:((((r2_hidden(esk2_3(X41,X42,X43),k2_relat_1(X43))|~r2_hidden(X41,k10_relat_1(X43,X42))|~v1_relat_1(X43))&(r2_hidden(k4_tarski(X41,esk2_3(X41,X42,X43)),X43)|~r2_hidden(X41,k10_relat_1(X43,X42))|~v1_relat_1(X43)))&(r2_hidden(esk2_3(X41,X42,X43),X42)|~r2_hidden(X41,k10_relat_1(X43,X42))|~v1_relat_1(X43)))&(~r2_hidden(X45,k2_relat_1(X43))|~r2_hidden(k4_tarski(X41,X45),X43)|~r2_hidden(X45,X42)|r2_hidden(X41,k10_relat_1(X43,X42))|~v1_relat_1(X43))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 24.16/24.40  fof(c_0_21, negated_conjecture, (v1_relat_1(esk4_0)&((~r2_hidden(esk3_0,k1_relat_1(esk4_0))|k11_relat_1(esk4_0,esk3_0)=k1_xboole_0)&(r2_hidden(esk3_0,k1_relat_1(esk4_0))|k11_relat_1(esk4_0,esk3_0)!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 24.16/24.40  fof(c_0_22, plain, ![X46]:(~v1_relat_1(X46)|k10_relat_1(X46,k2_relat_1(X46))=k1_relat_1(X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 24.16/24.40  fof(c_0_23, plain, ![X47, X48, X49]:((~r2_hidden(k4_tarski(X47,X48),X49)|r2_hidden(X48,k11_relat_1(X49,X47))|~v1_relat_1(X49))&(~r2_hidden(X48,k11_relat_1(X49,X47))|r2_hidden(k4_tarski(X47,X48),X49)|~v1_relat_1(X49))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 24.16/24.40  fof(c_0_24, plain, ![X7]:(X7=k1_xboole_0|r2_hidden(esk1_1(X7),X7)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 24.16/24.40  fof(c_0_25, plain, ![X50, X51, X52]:((r2_hidden(X50,k1_relat_1(X52))|~r2_hidden(k4_tarski(X50,X51),X52)|~v1_relat_1(X52))&(r2_hidden(X51,k2_relat_1(X52))|~r2_hidden(k4_tarski(X50,X51),X52)|~v1_relat_1(X52))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).
% 24.16/24.40  cnf(c_0_26, plain, (r2_hidden(k4_tarski(X1,esk2_3(X1,X2,X3)),X3)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 24.16/24.40  cnf(c_0_27, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 24.16/24.40  cnf(c_0_28, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 24.16/24.40  cnf(c_0_29, plain, (r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,k11_relat_1(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 24.16/24.40  cnf(c_0_30, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(esk4_0))|k11_relat_1(esk4_0,esk3_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 24.16/24.40  cnf(c_0_31, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 24.16/24.40  cnf(c_0_32, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 24.16/24.40  fof(c_0_33, plain, ![X39, X40]:k1_setfam_1(k2_tarski(X39,X40))=k3_xboole_0(X39,X40), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 24.16/24.40  fof(c_0_34, plain, ![X14, X15]:k1_enumset1(X14,X14,X15)=k2_tarski(X14,X15), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 24.16/24.40  cnf(c_0_35, negated_conjecture, (r2_hidden(k4_tarski(X1,esk2_3(X1,X2,esk4_0)),esk4_0)|~r2_hidden(X1,k10_relat_1(esk4_0,X2))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 24.16/24.40  cnf(c_0_36, negated_conjecture, (k10_relat_1(esk4_0,k2_relat_1(esk4_0))=k1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_28, c_0_27])).
% 24.16/24.40  cnf(c_0_37, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),esk4_0)|~r2_hidden(X2,k11_relat_1(esk4_0,X1))), inference(spm,[status(thm)],[c_0_29, c_0_27])).
% 24.16/24.40  cnf(c_0_38, negated_conjecture, (r2_hidden(esk1_1(k11_relat_1(esk4_0,esk3_0)),k11_relat_1(esk4_0,esk3_0))|r2_hidden(esk3_0,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 24.16/24.40  cnf(c_0_39, negated_conjecture, (r2_hidden(X1,k1_relat_1(esk4_0))|~r2_hidden(k4_tarski(X1,X2),esk4_0)), inference(spm,[status(thm)],[c_0_32, c_0_27])).
% 24.16/24.40  fof(c_0_40, plain, ![X9, X10]:k4_xboole_0(X9,X10)=k5_xboole_0(X9,k3_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 24.16/24.40  cnf(c_0_41, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 24.16/24.40  cnf(c_0_42, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 24.16/24.40  fof(c_0_43, plain, ![X34, X35]:((~r1_tarski(k1_tarski(X34),X35)|r2_hidden(X34,X35))&(~r2_hidden(X34,X35)|r1_tarski(k1_tarski(X34),X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 24.16/24.40  fof(c_0_44, plain, ![X13]:k2_tarski(X13,X13)=k1_tarski(X13), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 24.16/24.40  fof(c_0_45, plain, ![X16, X17, X18]:k2_enumset1(X16,X16,X17,X18)=k1_enumset1(X16,X17,X18), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 24.16/24.40  fof(c_0_46, plain, ![X19, X20, X21, X22]:k3_enumset1(X19,X19,X20,X21,X22)=k2_enumset1(X19,X20,X21,X22), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 24.16/24.40  fof(c_0_47, plain, ![X23, X24, X25, X26, X27]:k4_enumset1(X23,X23,X24,X25,X26,X27)=k3_enumset1(X23,X24,X25,X26,X27), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 24.16/24.40  fof(c_0_48, plain, ![X28, X29, X30, X31, X32, X33]:k5_enumset1(X28,X28,X29,X30,X31,X32,X33)=k4_enumset1(X28,X29,X30,X31,X32,X33), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 24.16/24.40  cnf(c_0_49, plain, (r2_hidden(X2,k11_relat_1(X3,X1))|~r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 24.16/24.40  cnf(c_0_50, negated_conjecture, (r2_hidden(k4_tarski(X1,esk2_3(X1,k2_relat_1(esk4_0),esk4_0)),esk4_0)|~r2_hidden(X1,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 24.16/24.40  cnf(c_0_51, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 24.16/24.40  cnf(c_0_52, negated_conjecture, (k11_relat_1(esk4_0,esk3_0)=k1_xboole_0|~r2_hidden(esk3_0,k1_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 24.16/24.40  fof(c_0_53, plain, ![X36, X37]:((k4_xboole_0(k1_tarski(X36),k1_tarski(X37))!=k1_tarski(X36)|X36!=X37)&(X36=X37|k4_xboole_0(k1_tarski(X36),k1_tarski(X37))=k1_tarski(X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 24.16/24.40  cnf(c_0_54, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 24.16/24.40  cnf(c_0_55, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 24.16/24.40  fof(c_0_56, plain, ![X38]:k1_setfam_1(k1_tarski(X38))=X38, inference(variable_rename,[status(thm)],[t11_setfam_1])).
% 24.16/24.40  cnf(c_0_57, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 24.16/24.40  cnf(c_0_58, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 24.16/24.40  cnf(c_0_59, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 24.16/24.40  cnf(c_0_60, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 24.16/24.40  cnf(c_0_61, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 24.16/24.40  cnf(c_0_62, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 24.16/24.40  cnf(c_0_63, negated_conjecture, (r2_hidden(X1,k11_relat_1(esk4_0,X2))|~r2_hidden(k4_tarski(X2,X1),esk4_0)), inference(spm,[status(thm)],[c_0_49, c_0_27])).
% 24.16/24.40  cnf(c_0_64, negated_conjecture, (r2_hidden(k4_tarski(esk3_0,esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0)),esk4_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 24.16/24.40  cnf(c_0_65, negated_conjecture, (k11_relat_1(esk4_0,esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_51])])).
% 24.16/24.40  cnf(c_0_66, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_53])).
% 24.16/24.40  cnf(c_0_67, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_54, c_0_55])).
% 24.16/24.40  cnf(c_0_68, plain, (k1_setfam_1(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_56])).
% 24.16/24.40  fof(c_0_69, plain, ![X12]:k5_xboole_0(X12,X12)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 24.16/24.40  fof(c_0_70, plain, ![X11]:(~r1_tarski(X11,k1_xboole_0)|X11=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 24.16/24.40  cnf(c_0_71, plain, (r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58]), c_0_42]), c_0_59]), c_0_60]), c_0_61]), c_0_62])).
% 24.16/24.40  cnf(c_0_72, negated_conjecture, (r2_hidden(esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0),k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])).
% 24.16/24.40  cnf(c_0_73, plain, (X1!=X2|k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2))))!=k5_enumset1(X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_58]), c_0_58]), c_0_58]), c_0_42]), c_0_42]), c_0_42]), c_0_67]), c_0_59]), c_0_59]), c_0_59]), c_0_59]), c_0_59]), c_0_59]), c_0_60]), c_0_60]), c_0_60]), c_0_60]), c_0_60]), c_0_60]), c_0_60]), c_0_61]), c_0_61]), c_0_61]), c_0_61]), c_0_61]), c_0_61]), c_0_61]), c_0_61]), c_0_62]), c_0_62]), c_0_62]), c_0_62]), c_0_62]), c_0_62]), c_0_62]), c_0_62]), c_0_62])).
% 24.16/24.40  cnf(c_0_74, plain, (k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_58]), c_0_42]), c_0_59]), c_0_60]), c_0_61]), c_0_62])).
% 24.16/24.40  cnf(c_0_75, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_69])).
% 24.16/24.40  cnf(c_0_76, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 24.16/24.40  cnf(c_0_77, negated_conjecture, (r1_tarski(k5_enumset1(esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0),esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0),esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0),esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0),esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0),esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0),esk2_3(esk3_0,k2_relat_1(esk4_0),esk4_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 24.16/24.40  cnf(c_0_78, plain, (k5_enumset1(X1,X1,X1,X1,X1,X1,X1)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_73]), c_0_74]), c_0_75])).
% 24.16/24.40  cnf(c_0_79, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78]), ['proof']).
% 24.16/24.40  # SZS output end CNFRefutation
% 24.16/24.40  # Proof object total steps             : 80
% 24.16/24.40  # Proof object clause steps            : 41
% 24.16/24.40  # Proof object formula steps           : 39
% 24.16/24.40  # Proof object conjectures             : 19
% 24.16/24.40  # Proof object clause conjectures      : 16
% 24.16/24.40  # Proof object formula conjectures     : 3
% 24.16/24.40  # Proof object initial clauses used    : 22
% 24.16/24.40  # Proof object initial formulas used   : 19
% 24.16/24.40  # Proof object generating inferences   : 12
% 24.16/24.40  # Proof object simplifying inferences  : 59
% 24.16/24.40  # Training examples: 0 positive, 0 negative
% 24.16/24.40  # Parsed axioms                        : 19
% 24.16/24.40  # Removed by relevancy pruning/SinE    : 0
% 24.16/24.40  # Initial clauses                      : 28
% 24.16/24.40  # Removed in clause preprocessing      : 8
% 24.16/24.40  # Initial clauses in saturation        : 20
% 24.16/24.40  # Processed clauses                    : 11006
% 24.16/24.40  # ...of these trivial                  : 87
% 24.16/24.40  # ...subsumed                          : 8376
% 24.16/24.40  # ...remaining for further processing  : 2543
% 24.16/24.40  # Other redundant clauses eliminated   : 195
% 24.16/24.40  # Clauses deleted for lack of memory   : 0
% 24.16/24.40  # Backward-subsumed                    : 347
% 24.16/24.40  # Backward-rewritten                   : 242
% 24.16/24.40  # Generated clauses                    : 611883
% 24.16/24.40  # ...of the previous two non-trivial   : 586389
% 24.16/24.40  # Contextual simplify-reflections      : 4
% 24.16/24.40  # Paramodulations                      : 611484
% 24.16/24.40  # Factorizations                       : 204
% 24.16/24.40  # Equation resolutions                 : 195
% 24.16/24.40  # Propositional unsat checks           : 0
% 24.16/24.40  #    Propositional check models        : 0
% 24.16/24.40  #    Propositional check unsatisfiable : 0
% 24.16/24.40  #    Propositional clauses             : 0
% 24.16/24.40  #    Propositional clauses after purity: 0
% 24.16/24.40  #    Propositional unsat core size     : 0
% 24.16/24.40  #    Propositional preprocessing time  : 0.000
% 24.16/24.40  #    Propositional encoding time       : 0.000
% 24.16/24.40  #    Propositional solver time         : 0.000
% 24.16/24.40  #    Success case prop preproc time    : 0.000
% 24.16/24.40  #    Success case prop encoding time   : 0.000
% 24.16/24.40  #    Success case prop solver time     : 0.000
% 24.16/24.40  # Current number of processed clauses  : 1933
% 24.16/24.40  #    Positive orientable unit clauses  : 45
% 24.16/24.40  #    Positive unorientable unit clauses: 0
% 24.16/24.40  #    Negative unit clauses             : 1
% 24.16/24.40  #    Non-unit-clauses                  : 1887
% 24.16/24.40  # Current number of unprocessed clauses: 573929
% 24.16/24.40  # ...number of literals in the above   : 3702885
% 24.16/24.40  # Current number of archived formulas  : 0
% 24.16/24.40  # Current number of archived clauses   : 617
% 24.16/24.40  # Clause-clause subsumption calls (NU) : 484339
% 24.16/24.40  # Rec. Clause-clause subsumption calls : 63332
% 24.16/24.40  # Non-unit clause-clause subsumptions  : 8718
% 24.16/24.40  # Unit Clause-clause subsumption calls : 5143
% 24.16/24.40  # Rewrite failures with RHS unbound    : 0
% 24.16/24.40  # BW rewrite match attempts            : 598
% 24.16/24.40  # BW rewrite match successes           : 52
% 24.16/24.40  # Condensation attempts                : 0
% 24.16/24.40  # Condensation successes               : 0
% 24.16/24.40  # Termbank termtop insertions          : 172405911
% 24.16/24.42  
% 24.16/24.42  # -------------------------------------------------
% 24.16/24.42  # User time                : 23.752 s
% 24.16/24.42  # System time              : 0.306 s
% 24.16/24.42  # Total time               : 24.057 s
% 24.16/24.42  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
