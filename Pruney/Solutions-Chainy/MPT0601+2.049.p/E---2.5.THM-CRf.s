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
% DateTime   : Thu Dec  3 10:52:19 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 237 expanded)
%              Number of clauses        :   38 (  91 expanded)
%              Number of leaves         :   17 (  70 expanded)
%              Depth                    :    9
%              Number of atoms          :  134 ( 389 expanded)
%              Number of equality atoms :   64 ( 228 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t205_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

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

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(t11_setfam_1,axiom,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k1_relat_1(X2))
        <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t205_relat_1])).

fof(c_0_18,plain,(
    ! [X52,X53,X54] :
      ( ( ~ r2_hidden(k4_tarski(X52,X53),X54)
        | r2_hidden(X53,k11_relat_1(X54,X52))
        | ~ v1_relat_1(X54) )
      & ( ~ r2_hidden(X53,k11_relat_1(X54,X52))
        | r2_hidden(k4_tarski(X52,X53),X54)
        | ~ v1_relat_1(X54) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

fof(c_0_19,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & ( ~ r2_hidden(esk5_0,k1_relat_1(esk6_0))
      | k11_relat_1(esk6_0,esk5_0) = k1_xboole_0 )
    & ( r2_hidden(esk5_0,k1_relat_1(esk6_0))
      | k11_relat_1(esk6_0,esk5_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_20,plain,(
    ! [X7] :
      ( X7 = k1_xboole_0
      | r2_hidden(esk1_1(X7),X7) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_21,plain,(
    ! [X41,X42,X43,X45,X46,X47,X48,X50] :
      ( ( ~ r2_hidden(X43,X42)
        | r2_hidden(k4_tarski(X43,esk2_3(X41,X42,X43)),X41)
        | X42 != k1_relat_1(X41) )
      & ( ~ r2_hidden(k4_tarski(X45,X46),X41)
        | r2_hidden(X45,X42)
        | X42 != k1_relat_1(X41) )
      & ( ~ r2_hidden(esk3_2(X47,X48),X48)
        | ~ r2_hidden(k4_tarski(esk3_2(X47,X48),X50),X47)
        | X48 = k1_relat_1(X47) )
      & ( r2_hidden(esk3_2(X47,X48),X48)
        | r2_hidden(k4_tarski(esk3_2(X47,X48),esk4_2(X47,X48)),X47)
        | X48 = k1_relat_1(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,k11_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk6_0))
    | k11_relat_1(esk6_0,esk5_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_27,plain,(
    ! [X39,X40] : k1_setfam_1(k2_tarski(X39,X40)) = k3_xboole_0(X39,X40) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_28,plain,(
    ! [X14,X15] : k1_enumset1(X14,X14,X15) = k2_tarski(X14,X15) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk6_0)
    | ~ r2_hidden(X2,k11_relat_1(esk6_0,X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk1_1(k11_relat_1(esk6_0,esk5_0)),k11_relat_1(esk6_0,esk5_0))
    | r2_hidden(esk5_0,k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_26])).

fof(c_0_33,plain,(
    ! [X9,X10] : k4_xboole_0(X9,X10) = k5_xboole_0(X9,k3_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_34,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_36,plain,(
    ! [X34,X35] :
      ( ( ~ r1_tarski(k1_tarski(X34),X35)
        | r2_hidden(X34,X35) )
      & ( ~ r2_hidden(X34,X35)
        | r1_tarski(k1_tarski(X34),X35) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_37,plain,(
    ! [X13] : k2_tarski(X13,X13) = k1_tarski(X13) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_38,plain,(
    ! [X16,X17,X18] : k2_enumset1(X16,X16,X17,X18) = k1_enumset1(X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_39,plain,(
    ! [X19,X20,X21,X22] : k3_enumset1(X19,X19,X20,X21,X22) = k2_enumset1(X19,X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_40,plain,(
    ! [X23,X24,X25,X26,X27] : k4_enumset1(X23,X23,X24,X25,X26,X27) = k3_enumset1(X23,X24,X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_41,plain,(
    ! [X28,X29,X30,X31,X32,X33] : k5_enumset1(X28,X28,X29,X30,X31,X32,X33) = k4_enumset1(X28,X29,X30,X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

cnf(c_0_42,plain,
    ( r2_hidden(X2,k11_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_43,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_45,negated_conjecture,
    ( k11_relat_1(esk6_0,esk5_0) = k1_xboole_0
    | ~ r2_hidden(esk5_0,k1_relat_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_46,plain,(
    ! [X36,X37] :
      ( ( k4_xboole_0(k1_tarski(X36),k1_tarski(X37)) != k1_tarski(X36)
        | X36 != X37 )
      & ( X36 = X37
        | k4_xboole_0(k1_tarski(X36),k1_tarski(X37)) = k1_tarski(X36) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_48,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_49,plain,(
    ! [X38] : k1_setfam_1(k1_tarski(X38)) = X38 ),
    inference(variable_rename,[status(thm)],[t11_setfam_1])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_51,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_52,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_53,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_54,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_55,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(X1,k11_relat_1(esk6_0,X2))
    | ~ r2_hidden(k4_tarski(X2,X1),esk6_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_23])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_58,negated_conjecture,
    ( k11_relat_1(esk6_0,esk5_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_44])])).

cnf(c_0_59,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_60,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_61,plain,
    ( k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_62,plain,(
    ! [X12] : k5_xboole_0(X12,X12) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_63,plain,(
    ! [X11] :
      ( ~ r1_tarski(X11,k1_xboole_0)
      | X11 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_64,plain,
    ( r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51]),c_0_35]),c_0_52]),c_0_53]),c_0_54]),c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_66,plain,
    ( X1 != X2
    | k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2)))) != k5_enumset1(X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_51]),c_0_51]),c_0_51]),c_0_35]),c_0_35]),c_0_35]),c_0_60]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_55]),c_0_55]),c_0_55]),c_0_55]),c_0_55]),c_0_55]),c_0_55]),c_0_55]),c_0_55])).

cnf(c_0_67,plain,
    ( k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_51]),c_0_35]),c_0_52]),c_0_53]),c_0_54]),c_0_55])).

cnf(c_0_68,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_69,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(k5_enumset1(esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_71,plain,
    ( k5_enumset1(X1,X1,X1,X1,X1,X1,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_66]),c_0_67]),c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:11:46 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.71/1.96  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 1.71/1.96  # and selection function SelectNegativeLiterals.
% 1.71/1.96  #
% 1.71/1.96  # Preprocessing time       : 0.036 s
% 1.71/1.96  # Presaturation interreduction done
% 1.71/1.96  
% 1.71/1.96  # Proof found!
% 1.71/1.96  # SZS status Theorem
% 1.71/1.96  # SZS output start CNFRefutation
% 1.71/1.96  fof(t205_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 1.71/1.96  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 1.71/1.96  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.71/1.96  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 1.71/1.96  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.71/1.96  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.71/1.96  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.71/1.96  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.71/1.96  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.71/1.96  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.71/1.96  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.71/1.96  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 1.71/1.96  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 1.71/1.96  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.71/1.96  fof(t11_setfam_1, axiom, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 1.71/1.96  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.71/1.96  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.71/1.96  fof(c_0_17, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t205_relat_1])).
% 1.71/1.96  fof(c_0_18, plain, ![X52, X53, X54]:((~r2_hidden(k4_tarski(X52,X53),X54)|r2_hidden(X53,k11_relat_1(X54,X52))|~v1_relat_1(X54))&(~r2_hidden(X53,k11_relat_1(X54,X52))|r2_hidden(k4_tarski(X52,X53),X54)|~v1_relat_1(X54))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 1.71/1.96  fof(c_0_19, negated_conjecture, (v1_relat_1(esk6_0)&((~r2_hidden(esk5_0,k1_relat_1(esk6_0))|k11_relat_1(esk6_0,esk5_0)=k1_xboole_0)&(r2_hidden(esk5_0,k1_relat_1(esk6_0))|k11_relat_1(esk6_0,esk5_0)!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 1.71/1.96  fof(c_0_20, plain, ![X7]:(X7=k1_xboole_0|r2_hidden(esk1_1(X7),X7)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 1.71/1.96  fof(c_0_21, plain, ![X41, X42, X43, X45, X46, X47, X48, X50]:(((~r2_hidden(X43,X42)|r2_hidden(k4_tarski(X43,esk2_3(X41,X42,X43)),X41)|X42!=k1_relat_1(X41))&(~r2_hidden(k4_tarski(X45,X46),X41)|r2_hidden(X45,X42)|X42!=k1_relat_1(X41)))&((~r2_hidden(esk3_2(X47,X48),X48)|~r2_hidden(k4_tarski(esk3_2(X47,X48),X50),X47)|X48=k1_relat_1(X47))&(r2_hidden(esk3_2(X47,X48),X48)|r2_hidden(k4_tarski(esk3_2(X47,X48),esk4_2(X47,X48)),X47)|X48=k1_relat_1(X47)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 1.71/1.96  cnf(c_0_22, plain, (r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,k11_relat_1(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.71/1.96  cnf(c_0_23, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.71/1.96  cnf(c_0_24, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(esk6_0))|k11_relat_1(esk6_0,esk5_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.71/1.96  cnf(c_0_25, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.71/1.96  cnf(c_0_26, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.71/1.96  fof(c_0_27, plain, ![X39, X40]:k1_setfam_1(k2_tarski(X39,X40))=k3_xboole_0(X39,X40), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 1.71/1.96  fof(c_0_28, plain, ![X14, X15]:k1_enumset1(X14,X14,X15)=k2_tarski(X14,X15), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.71/1.96  cnf(c_0_29, plain, (r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.71/1.96  cnf(c_0_30, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),esk6_0)|~r2_hidden(X2,k11_relat_1(esk6_0,X1))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 1.71/1.96  cnf(c_0_31, negated_conjecture, (r2_hidden(esk1_1(k11_relat_1(esk6_0,esk5_0)),k11_relat_1(esk6_0,esk5_0))|r2_hidden(esk5_0,k1_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 1.71/1.96  cnf(c_0_32, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_26])).
% 1.71/1.96  fof(c_0_33, plain, ![X9, X10]:k4_xboole_0(X9,X10)=k5_xboole_0(X9,k3_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 1.71/1.96  cnf(c_0_34, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.71/1.96  cnf(c_0_35, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.71/1.96  fof(c_0_36, plain, ![X34, X35]:((~r1_tarski(k1_tarski(X34),X35)|r2_hidden(X34,X35))&(~r2_hidden(X34,X35)|r1_tarski(k1_tarski(X34),X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 1.71/1.96  fof(c_0_37, plain, ![X13]:k2_tarski(X13,X13)=k1_tarski(X13), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.71/1.96  fof(c_0_38, plain, ![X16, X17, X18]:k2_enumset1(X16,X16,X17,X18)=k1_enumset1(X16,X17,X18), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.71/1.96  fof(c_0_39, plain, ![X19, X20, X21, X22]:k3_enumset1(X19,X19,X20,X21,X22)=k2_enumset1(X19,X20,X21,X22), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 1.71/1.96  fof(c_0_40, plain, ![X23, X24, X25, X26, X27]:k4_enumset1(X23,X23,X24,X25,X26,X27)=k3_enumset1(X23,X24,X25,X26,X27), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 1.71/1.96  fof(c_0_41, plain, ![X28, X29, X30, X31, X32, X33]:k5_enumset1(X28,X28,X29,X30,X31,X32,X33)=k4_enumset1(X28,X29,X30,X31,X32,X33), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 1.71/1.96  cnf(c_0_42, plain, (r2_hidden(X2,k11_relat_1(X3,X1))|~r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.71/1.96  cnf(c_0_43, plain, (r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_29])).
% 1.71/1.96  cnf(c_0_44, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 1.71/1.96  cnf(c_0_45, negated_conjecture, (k11_relat_1(esk6_0,esk5_0)=k1_xboole_0|~r2_hidden(esk5_0,k1_relat_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.71/1.96  fof(c_0_46, plain, ![X36, X37]:((k4_xboole_0(k1_tarski(X36),k1_tarski(X37))!=k1_tarski(X36)|X36!=X37)&(X36=X37|k4_xboole_0(k1_tarski(X36),k1_tarski(X37))=k1_tarski(X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 1.71/1.96  cnf(c_0_47, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.71/1.96  cnf(c_0_48, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 1.71/1.96  fof(c_0_49, plain, ![X38]:k1_setfam_1(k1_tarski(X38))=X38, inference(variable_rename,[status(thm)],[t11_setfam_1])).
% 1.71/1.96  cnf(c_0_50, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.71/1.96  cnf(c_0_51, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 1.71/1.96  cnf(c_0_52, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 1.71/1.96  cnf(c_0_53, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.71/1.96  cnf(c_0_54, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.71/1.96  cnf(c_0_55, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.71/1.96  cnf(c_0_56, negated_conjecture, (r2_hidden(X1,k11_relat_1(esk6_0,X2))|~r2_hidden(k4_tarski(X2,X1),esk6_0)), inference(spm,[status(thm)],[c_0_42, c_0_23])).
% 1.71/1.96  cnf(c_0_57, negated_conjecture, (r2_hidden(k4_tarski(esk5_0,esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0)),esk6_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 1.71/1.96  cnf(c_0_58, negated_conjecture, (k11_relat_1(esk6_0,esk5_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_44])])).
% 1.71/1.96  cnf(c_0_59, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_46])).
% 1.71/1.96  cnf(c_0_60, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 1.71/1.96  cnf(c_0_61, plain, (k1_setfam_1(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_49])).
% 1.71/1.96  fof(c_0_62, plain, ![X12]:k5_xboole_0(X12,X12)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 1.71/1.96  fof(c_0_63, plain, ![X11]:(~r1_tarski(X11,k1_xboole_0)|X11=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 1.71/1.96  cnf(c_0_64, plain, (r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51]), c_0_35]), c_0_52]), c_0_53]), c_0_54]), c_0_55])).
% 1.71/1.96  cnf(c_0_65, negated_conjecture, (r2_hidden(esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 1.71/1.96  cnf(c_0_66, plain, (X1!=X2|k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2))))!=k5_enumset1(X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_51]), c_0_51]), c_0_51]), c_0_35]), c_0_35]), c_0_35]), c_0_60]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_54]), c_0_54]), c_0_54]), c_0_54]), c_0_54]), c_0_54]), c_0_54]), c_0_54]), c_0_55]), c_0_55]), c_0_55]), c_0_55]), c_0_55]), c_0_55]), c_0_55]), c_0_55]), c_0_55])).
% 1.71/1.96  cnf(c_0_67, plain, (k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_51]), c_0_35]), c_0_52]), c_0_53]), c_0_54]), c_0_55])).
% 1.71/1.96  cnf(c_0_68, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_62])).
% 1.71/1.96  cnf(c_0_69, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 1.71/1.96  cnf(c_0_70, negated_conjecture, (r1_tarski(k5_enumset1(esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 1.71/1.96  cnf(c_0_71, plain, (k5_enumset1(X1,X1,X1,X1,X1,X1,X1)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_66]), c_0_67]), c_0_68])).
% 1.71/1.96  cnf(c_0_72, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71]), ['proof']).
% 1.71/1.96  # SZS output end CNFRefutation
% 1.71/1.96  # Proof object total steps             : 73
% 1.71/1.96  # Proof object clause steps            : 38
% 1.71/1.96  # Proof object formula steps           : 35
% 1.71/1.96  # Proof object conjectures             : 15
% 1.71/1.96  # Proof object clause conjectures      : 12
% 1.71/1.96  # Proof object formula conjectures     : 3
% 1.71/1.96  # Proof object initial clauses used    : 21
% 1.71/1.96  # Proof object initial formulas used   : 17
% 1.71/1.96  # Proof object generating inferences   : 8
% 1.71/1.96  # Proof object simplifying inferences  : 61
% 1.71/1.96  # Training examples: 0 positive, 0 negative
% 1.71/1.96  # Parsed axioms                        : 17
% 1.71/1.96  # Removed by relevancy pruning/SinE    : 0
% 1.71/1.96  # Initial clauses                      : 25
% 1.71/1.96  # Removed in clause preprocessing      : 8
% 1.71/1.96  # Initial clauses in saturation        : 17
% 1.71/1.96  # Processed clauses                    : 3317
% 1.71/1.96  # ...of these trivial                  : 8
% 1.71/1.96  # ...subsumed                          : 2631
% 1.71/1.96  # ...remaining for further processing  : 678
% 1.71/1.96  # Other redundant clauses eliminated   : 91
% 1.71/1.96  # Clauses deleted for lack of memory   : 0
% 1.71/1.96  # Backward-subsumed                    : 92
% 1.71/1.96  # Backward-rewritten                   : 84
% 1.71/1.96  # Generated clauses                    : 104658
% 1.71/1.96  # ...of the previous two non-trivial   : 97775
% 1.71/1.96  # Contextual simplify-reflections      : 5
% 1.71/1.96  # Paramodulations                      : 104479
% 1.71/1.96  # Factorizations                       : 88
% 1.71/1.96  # Equation resolutions                 : 91
% 1.71/1.96  # Propositional unsat checks           : 0
% 1.71/1.96  #    Propositional check models        : 0
% 1.71/1.96  #    Propositional check unsatisfiable : 0
% 1.71/1.96  #    Propositional clauses             : 0
% 1.71/1.96  #    Propositional clauses after purity: 0
% 1.71/1.96  #    Propositional unsat core size     : 0
% 1.71/1.96  #    Propositional preprocessing time  : 0.000
% 1.71/1.96  #    Propositional encoding time       : 0.000
% 1.71/1.96  #    Propositional solver time         : 0.000
% 1.71/1.96  #    Success case prop preproc time    : 0.000
% 1.71/1.96  #    Success case prop encoding time   : 0.000
% 1.71/1.96  #    Success case prop solver time     : 0.000
% 1.71/1.96  # Current number of processed clauses  : 482
% 1.71/1.96  #    Positive orientable unit clauses  : 13
% 1.71/1.96  #    Positive unorientable unit clauses: 0
% 1.71/1.96  #    Negative unit clauses             : 1
% 1.71/1.96  #    Non-unit-clauses                  : 468
% 1.71/1.96  # Current number of unprocessed clauses: 94014
% 1.71/1.96  # ...number of literals in the above   : 584032
% 1.71/1.96  # Current number of archived formulas  : 0
% 1.71/1.96  # Current number of archived clauses   : 201
% 1.71/1.96  # Clause-clause subsumption calls (NU) : 66304
% 1.71/1.96  # Rec. Clause-clause subsumption calls : 9948
% 1.71/1.96  # Non-unit clause-clause subsumptions  : 2726
% 1.71/1.96  # Unit Clause-clause subsumption calls : 742
% 1.71/1.96  # Rewrite failures with RHS unbound    : 0
% 1.71/1.96  # BW rewrite match attempts            : 181
% 1.71/1.96  # BW rewrite match successes           : 28
% 1.71/1.96  # Condensation attempts                : 0
% 1.71/1.96  # Condensation successes               : 0
% 1.71/1.96  # Termbank termtop insertions          : 7141540
% 1.71/1.96  
% 1.71/1.96  # -------------------------------------------------
% 1.71/1.96  # User time                : 1.553 s
% 1.71/1.96  # System time              : 0.047 s
% 1.71/1.96  # Total time               : 1.600 s
% 1.71/1.96  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
