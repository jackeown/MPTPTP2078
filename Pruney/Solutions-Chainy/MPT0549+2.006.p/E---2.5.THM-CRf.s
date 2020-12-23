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
% DateTime   : Thu Dec  3 10:50:44 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 111 expanded)
%              Number of clauses        :   35 (  45 expanded)
%              Number of leaves         :   20 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :  142 ( 253 expanded)
%              Number of equality atoms :   52 (  94 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t55_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r1_xboole_0(k2_tarski(X1,X2),X3)
        & r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

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

fof(t151_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k9_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(t95_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k7_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(t127_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_xboole_0(X1,X2)
        | r1_xboole_0(X3,X4) )
     => r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(t98_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_xboole_0(X3,X2) )
     => r1_xboole_0(k3_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_zfmisc_1)).

fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t2_zfmisc_1,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_20,plain,(
    ! [X44,X45,X46] :
      ( ~ r1_xboole_0(k2_tarski(X44,X45),X46)
      | ~ r2_hidden(X44,X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_zfmisc_1])])).

fof(c_0_21,plain,(
    ! [X13,X14] : k1_enumset1(X13,X13,X14) = k2_tarski(X13,X14) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X15,X16,X17] : k2_enumset1(X15,X15,X16,X17) = k1_enumset1(X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_23,plain,(
    ! [X18,X19,X20,X21] : k3_enumset1(X18,X18,X19,X20,X21) = k2_enumset1(X18,X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_24,plain,(
    ! [X22,X23,X24,X25,X26] : k4_enumset1(X22,X22,X23,X24,X25,X26) = k3_enumset1(X22,X23,X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_25,plain,(
    ! [X27,X28,X29,X30,X31,X32] : k5_enumset1(X27,X27,X28,X29,X30,X31,X32) = k4_enumset1(X27,X28,X29,X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_26,plain,(
    ! [X33,X34,X35,X36,X37,X38,X39] : k6_enumset1(X33,X33,X34,X35,X36,X37,X38,X39) = k5_enumset1(X33,X34,X35,X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k9_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t151_relat_1])).

fof(c_0_28,plain,(
    ! [X52,X53] :
      ( ~ v1_relat_1(X53)
      | k2_relat_1(k7_relat_1(X53,X52)) = k9_relat_1(X53,X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_29,plain,(
    ! [X55,X56] :
      ( ( k7_relat_1(X56,X55) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X56),X55)
        | ~ v1_relat_1(X56) )
      & ( ~ r1_xboole_0(k1_relat_1(X56),X55)
        | k7_relat_1(X56,X55) = k1_xboole_0
        | ~ v1_relat_1(X56) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_relat_1])])])).

cnf(c_0_30,plain,
    ( ~ r1_xboole_0(k2_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_37,plain,(
    ! [X11] : r1_xboole_0(X11,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_38,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & ( k9_relat_1(esk3_0,esk2_0) != k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(esk3_0),esk2_0) )
    & ( k9_relat_1(esk3_0,esk2_0) = k1_xboole_0
      | r1_xboole_0(k1_relat_1(esk3_0),esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

cnf(c_0_39,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

fof(c_0_42,plain,(
    ! [X12] :
      ( ( r1_xboole_0(X12,X12)
        | X12 != k1_xboole_0 )
      & ( X12 = k1_xboole_0
        | ~ r1_xboole_0(X12,X12) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

fof(c_0_43,plain,(
    ! [X40,X41,X42,X43] :
      ( ( ~ r1_xboole_0(X40,X41)
        | r1_xboole_0(k2_zfmisc_1(X40,X42),k2_zfmisc_1(X41,X43)) )
      & ( ~ r1_xboole_0(X42,X43)
        | r1_xboole_0(k2_zfmisc_1(X40,X42),k2_zfmisc_1(X41,X43)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_45,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_46,plain,(
    ! [X47,X48] :
      ( ( r2_hidden(esk1_2(X47,X48),X47)
        | r1_xboole_0(k3_tarski(X47),X48) )
      & ( ~ r1_xboole_0(esk1_2(X47,X48),X48)
        | r1_xboole_0(k3_tarski(X47),X48) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_zfmisc_1])])])])).

fof(c_0_47,plain,(
    ! [X54] :
      ( ~ v1_relat_1(X54)
      | r1_tarski(X54,k2_zfmisc_1(k1_relat_1(X54),k2_relat_1(X54))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

fof(c_0_48,plain,(
    ! [X50,X51] :
      ( ~ v1_relat_1(X50)
      | v1_relat_1(k7_relat_1(X50,X51)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_49,negated_conjecture,
    ( k9_relat_1(esk3_0,esk2_0) != k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,plain,
    ( k9_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k1_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_55,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(k3_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t2_zfmisc_1])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( k9_relat_1(esk3_0,esk2_0) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_60,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])])).

cnf(c_0_61,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_62,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

fof(c_0_63,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_64,plain,
    ( r1_tarski(k7_relat_1(X1,X2),k2_zfmisc_1(k1_relat_1(k7_relat_1(X1,X2)),k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_39]),c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( k9_relat_1(esk3_0,esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

fof(c_0_67,plain,(
    ! [X10] : r1_tarski(k1_xboole_0,X10) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_68,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk3_0,esk2_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66]),c_0_51])])).

cnf(c_0_70,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_71,plain,
    ( r1_xboole_0(k1_relat_1(X1),X2)
    | k7_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_72,negated_conjecture,
    ( k7_relat_1(esk3_0,esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_51])]),c_0_60]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.20/0.38  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.027 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t55_zfmisc_1, axiom, ![X1, X2, X3]:~((r1_xboole_0(k2_tarski(X1,X2),X3)&r2_hidden(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 0.20/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.38  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.38  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.20/0.38  fof(t151_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k9_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 0.20/0.38  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.20/0.38  fof(t95_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 0.20/0.38  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.20/0.38  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.20/0.38  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 0.20/0.38  fof(t127_zfmisc_1, axiom, ![X1, X2, X3, X4]:((r1_xboole_0(X1,X2)|r1_xboole_0(X3,X4))=>r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 0.20/0.38  fof(t98_zfmisc_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_xboole_0(X3,X2))=>r1_xboole_0(k3_tarski(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_zfmisc_1)).
% 0.20/0.38  fof(t21_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 0.20/0.38  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.20/0.38  fof(t2_zfmisc_1, axiom, k3_tarski(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 0.20/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.38  fof(c_0_20, plain, ![X44, X45, X46]:(~r1_xboole_0(k2_tarski(X44,X45),X46)|~r2_hidden(X44,X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_zfmisc_1])])).
% 0.20/0.38  fof(c_0_21, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.38  fof(c_0_22, plain, ![X15, X16, X17]:k2_enumset1(X15,X15,X16,X17)=k1_enumset1(X15,X16,X17), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.38  fof(c_0_23, plain, ![X18, X19, X20, X21]:k3_enumset1(X18,X18,X19,X20,X21)=k2_enumset1(X18,X19,X20,X21), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.38  fof(c_0_24, plain, ![X22, X23, X24, X25, X26]:k4_enumset1(X22,X22,X23,X24,X25,X26)=k3_enumset1(X22,X23,X24,X25,X26), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.38  fof(c_0_25, plain, ![X27, X28, X29, X30, X31, X32]:k5_enumset1(X27,X27,X28,X29,X30,X31,X32)=k4_enumset1(X27,X28,X29,X30,X31,X32), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.38  fof(c_0_26, plain, ![X33, X34, X35, X36, X37, X38, X39]:k6_enumset1(X33,X33,X34,X35,X36,X37,X38,X39)=k5_enumset1(X33,X34,X35,X36,X37,X38,X39), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.20/0.38  fof(c_0_27, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k9_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t151_relat_1])).
% 0.20/0.38  fof(c_0_28, plain, ![X52, X53]:(~v1_relat_1(X53)|k2_relat_1(k7_relat_1(X53,X52))=k9_relat_1(X53,X52)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.20/0.38  fof(c_0_29, plain, ![X55, X56]:((k7_relat_1(X56,X55)!=k1_xboole_0|r1_xboole_0(k1_relat_1(X56),X55)|~v1_relat_1(X56))&(~r1_xboole_0(k1_relat_1(X56),X55)|k7_relat_1(X56,X55)=k1_xboole_0|~v1_relat_1(X56))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_relat_1])])])).
% 0.20/0.38  cnf(c_0_30, plain, (~r1_xboole_0(k2_tarski(X1,X2),X3)|~r2_hidden(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_31, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.38  cnf(c_0_32, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.38  cnf(c_0_33, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_34, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_35, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.38  cnf(c_0_36, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  fof(c_0_37, plain, ![X11]:r1_xboole_0(X11,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.20/0.38  fof(c_0_38, negated_conjecture, (v1_relat_1(esk3_0)&((k9_relat_1(esk3_0,esk2_0)!=k1_xboole_0|~r1_xboole_0(k1_relat_1(esk3_0),esk2_0))&(k9_relat_1(esk3_0,esk2_0)=k1_xboole_0|r1_xboole_0(k1_relat_1(esk3_0),esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).
% 0.20/0.38  cnf(c_0_39, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.38  cnf(c_0_40, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~r1_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.38  cnf(c_0_41, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.20/0.38  fof(c_0_42, plain, ![X12]:((r1_xboole_0(X12,X12)|X12!=k1_xboole_0)&(X12=k1_xboole_0|~r1_xboole_0(X12,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 0.20/0.38  fof(c_0_43, plain, ![X40, X41, X42, X43]:((~r1_xboole_0(X40,X41)|r1_xboole_0(k2_zfmisc_1(X40,X42),k2_zfmisc_1(X41,X43)))&(~r1_xboole_0(X42,X43)|r1_xboole_0(k2_zfmisc_1(X40,X42),k2_zfmisc_1(X41,X43)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).
% 0.20/0.38  cnf(c_0_44, plain, (~r2_hidden(X1,X3)|~r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36])).
% 0.20/0.38  cnf(c_0_45, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.38  fof(c_0_46, plain, ![X47, X48]:((r2_hidden(esk1_2(X47,X48),X47)|r1_xboole_0(k3_tarski(X47),X48))&(~r1_xboole_0(esk1_2(X47,X48),X48)|r1_xboole_0(k3_tarski(X47),X48))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_zfmisc_1])])])])).
% 0.20/0.38  fof(c_0_47, plain, ![X54]:(~v1_relat_1(X54)|r1_tarski(X54,k2_zfmisc_1(k1_relat_1(X54),k2_relat_1(X54)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).
% 0.20/0.38  fof(c_0_48, plain, ![X50, X51]:(~v1_relat_1(X50)|v1_relat_1(k7_relat_1(X50,X51))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.20/0.38  cnf(c_0_49, negated_conjecture, (k9_relat_1(esk3_0,esk2_0)!=k1_xboole_0|~r1_xboole_0(k1_relat_1(esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.38  cnf(c_0_50, plain, (k9_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(k1_relat_1(X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.20/0.38  cnf(c_0_51, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.38  cnf(c_0_52, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.38  cnf(c_0_53, plain, (r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.38  cnf(c_0_54, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.38  cnf(c_0_55, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(k3_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.38  cnf(c_0_56, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t2_zfmisc_1])).
% 0.20/0.38  cnf(c_0_57, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.38  cnf(c_0_58, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.38  cnf(c_0_59, negated_conjecture, (k9_relat_1(esk3_0,esk2_0)=k1_xboole_0|r1_xboole_0(k1_relat_1(esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.38  cnf(c_0_60, negated_conjecture, (~r1_xboole_0(k1_relat_1(esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])])).
% 0.20/0.38  cnf(c_0_61, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.38  cnf(c_0_62, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 0.20/0.38  fof(c_0_63, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.38  cnf(c_0_64, plain, (r1_tarski(k7_relat_1(X1,X2),k2_zfmisc_1(k1_relat_1(k7_relat_1(X1,X2)),k9_relat_1(X1,X2)))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_39]), c_0_58])).
% 0.20/0.38  cnf(c_0_65, negated_conjecture, (k9_relat_1(esk3_0,esk2_0)=k1_xboole_0), inference(sr,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.38  cnf(c_0_66, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.38  fof(c_0_67, plain, ![X10]:r1_tarski(k1_xboole_0,X10), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.38  cnf(c_0_68, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.38  cnf(c_0_69, negated_conjecture, (r1_tarski(k7_relat_1(esk3_0,esk2_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66]), c_0_51])])).
% 0.20/0.38  cnf(c_0_70, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.38  cnf(c_0_71, plain, (r1_xboole_0(k1_relat_1(X1),X2)|k7_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.38  cnf(c_0_72, negated_conjecture, (k7_relat_1(esk3_0,esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])])).
% 0.20/0.38  cnf(c_0_73, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_51])]), c_0_60]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 74
% 0.20/0.38  # Proof object clause steps            : 35
% 0.20/0.38  # Proof object formula steps           : 39
% 0.20/0.38  # Proof object conjectures             : 11
% 0.20/0.38  # Proof object clause conjectures      : 8
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 23
% 0.20/0.38  # Proof object initial formulas used   : 20
% 0.20/0.38  # Proof object generating inferences   : 10
% 0.20/0.38  # Proof object simplifying inferences  : 20
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 20
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 29
% 0.20/0.38  # Removed in clause preprocessing      : 6
% 0.20/0.38  # Initial clauses in saturation        : 23
% 0.20/0.38  # Processed clauses                    : 74
% 0.20/0.38  # ...of these trivial                  : 2
% 0.20/0.38  # ...subsumed                          : 1
% 0.20/0.38  # ...remaining for further processing  : 71
% 0.20/0.38  # Other redundant clauses eliminated   : 3
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 2
% 0.20/0.38  # Backward-rewritten                   : 2
% 0.20/0.38  # Generated clauses                    : 113
% 0.20/0.38  # ...of the previous two non-trivial   : 48
% 0.20/0.38  # Contextual simplify-reflections      : 1
% 0.20/0.38  # Paramodulations                      : 109
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 3
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 42
% 0.20/0.38  #    Positive orientable unit clauses  : 13
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 2
% 0.20/0.38  #    Non-unit-clauses                  : 27
% 0.20/0.38  # Current number of unprocessed clauses: 17
% 0.20/0.38  # ...number of literals in the above   : 37
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 32
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 147
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 126
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.20/0.38  # Unit Clause-clause subsumption calls : 13
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 4
% 0.20/0.38  # BW rewrite match successes           : 3
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 2735
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.031 s
% 0.20/0.38  # System time              : 0.004 s
% 0.20/0.38  # Total time               : 0.034 s
% 0.20/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
