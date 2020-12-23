%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:38 EST 2020

% Result     : Theorem 0.72s
% Output     : CNFRefutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 338 expanded)
%              Number of clauses        :   32 ( 122 expanded)
%              Number of leaves         :   19 ( 108 expanded)
%              Depth                    :    8
%              Number of atoms          :  108 ( 376 expanded)
%              Number of equality atoms :   60 ( 328 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   14 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t150_relat_1,conjecture,(
    ! [X1] : k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

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

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t19_zfmisc_1,axiom,(
    ! [X1,X2] : k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(c_0_19,plain,(
    ! [X48,X49] : k1_setfam_1(k2_tarski(X48,X49)) = k3_xboole_0(X48,X49) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_20,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X50] : v1_relat_1(k6_relat_1(X50)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1] : k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t150_relat_1])).

fof(c_0_23,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_24,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X51,X52,X53,X55] :
      ( ( r2_hidden(esk2_3(X51,X52,X53),k1_relat_1(X53))
        | ~ r2_hidden(X51,k9_relat_1(X53,X52))
        | ~ v1_relat_1(X53) )
      & ( r2_hidden(k4_tarski(esk2_3(X51,X52,X53),X51),X53)
        | ~ r2_hidden(X51,k9_relat_1(X53,X52))
        | ~ v1_relat_1(X53) )
      & ( r2_hidden(esk2_3(X51,X52,X53),X52)
        | ~ r2_hidden(X51,k9_relat_1(X53,X52))
        | ~ v1_relat_1(X53) )
      & ( ~ r2_hidden(X55,k1_relat_1(X53))
        | ~ r2_hidden(k4_tarski(X55,X51),X53)
        | ~ r2_hidden(X55,X52)
        | r2_hidden(X51,k9_relat_1(X53,X52))
        | ~ v1_relat_1(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

cnf(c_0_27,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

fof(c_0_29,negated_conjecture,(
    k9_relat_1(k1_xboole_0,esk3_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

fof(c_0_30,plain,(
    ! [X8] :
      ( X8 = k1_xboole_0
      | r2_hidden(esk1_1(X8),X8) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_31,plain,(
    ! [X46,X47] :
      ( ( k4_xboole_0(k1_tarski(X46),k1_tarski(X47)) != k1_tarski(X46)
        | X46 != X47 )
      & ( X46 = X47
        | k4_xboole_0(k1_tarski(X46),k1_tarski(X47)) = k1_tarski(X46) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

fof(c_0_32,plain,(
    ! [X14] : k2_tarski(X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_35,plain,(
    ! [X17,X18,X19] : k2_enumset1(X17,X17,X18,X19) = k1_enumset1(X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_36,plain,(
    ! [X20,X21,X22,X23] : k3_enumset1(X20,X20,X21,X22,X23) = k2_enumset1(X20,X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_37,plain,(
    ! [X24,X25,X26,X27,X28] : k4_enumset1(X24,X24,X25,X26,X27,X28) = k3_enumset1(X24,X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_38,plain,(
    ! [X29,X30,X31,X32,X33,X34] : k5_enumset1(X29,X29,X30,X31,X32,X33,X34) = k4_enumset1(X29,X30,X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_39,plain,(
    ! [X35,X36,X37,X38,X39,X40,X41] : k6_enumset1(X35,X35,X36,X37,X38,X39,X40,X41) = k5_enumset1(X35,X36,X37,X38,X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_40,plain,(
    ! [X42,X43] :
      ( ( ~ r1_tarski(k1_tarski(X42),X43)
        | r2_hidden(X42,X43) )
      & ( ~ r2_hidden(X42,X43)
        | r1_tarski(k1_tarski(X42),X43) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_41,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_43,negated_conjecture,
    ( k9_relat_1(k1_xboole_0,esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_45,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_48,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_49,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_50,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_53,plain,(
    ! [X44,X45] : k3_xboole_0(k1_tarski(X44),k2_tarski(X44,X45)) = k1_tarski(X44) ),
    inference(variable_rename,[status(thm)],[t19_zfmisc_1])).

cnf(c_0_54,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_55,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X2,k1_xboole_0),X1),k1_xboole_0)
    | ~ r2_hidden(X1,k9_relat_1(k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk1_1(k9_relat_1(k1_xboole_0,esk3_0)),k9_relat_1(k1_xboole_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_57,plain,
    ( X1 != X2
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_46]),c_0_46]),c_0_25]),c_0_25]),c_0_25]),c_0_47]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52])).

cnf(c_0_58,plain,
    ( k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_59,plain,(
    ! [X13] : k5_xboole_0(X13,X13) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_60,plain,(
    ! [X12] :
      ( ~ r1_tarski(X12,k1_xboole_0)
      | X12 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_61,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_46]),c_0_25]),c_0_48]),c_0_49]),c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_3(esk1_1(k9_relat_1(k1_xboole_0,esk3_0)),esk3_0,k1_xboole_0),esk1_1(k9_relat_1(k1_xboole_0,esk3_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_64,plain,
    ( k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_46]),c_0_46]),c_0_25]),c_0_25]),c_0_25]),c_0_34]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52])).

cnf(c_0_65,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_66,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k6_enumset1(k4_tarski(esk2_3(esk1_1(k9_relat_1(k1_xboole_0,esk3_0)),esk3_0,k1_xboole_0),esk1_1(k9_relat_1(k1_xboole_0,esk3_0))),k4_tarski(esk2_3(esk1_1(k9_relat_1(k1_xboole_0,esk3_0)),esk3_0,k1_xboole_0),esk1_1(k9_relat_1(k1_xboole_0,esk3_0))),k4_tarski(esk2_3(esk1_1(k9_relat_1(k1_xboole_0,esk3_0)),esk3_0,k1_xboole_0),esk1_1(k9_relat_1(k1_xboole_0,esk3_0))),k4_tarski(esk2_3(esk1_1(k9_relat_1(k1_xboole_0,esk3_0)),esk3_0,k1_xboole_0),esk1_1(k9_relat_1(k1_xboole_0,esk3_0))),k4_tarski(esk2_3(esk1_1(k9_relat_1(k1_xboole_0,esk3_0)),esk3_0,k1_xboole_0),esk1_1(k9_relat_1(k1_xboole_0,esk3_0))),k4_tarski(esk2_3(esk1_1(k9_relat_1(k1_xboole_0,esk3_0)),esk3_0,k1_xboole_0),esk1_1(k9_relat_1(k1_xboole_0,esk3_0))),k4_tarski(esk2_3(esk1_1(k9_relat_1(k1_xboole_0,esk3_0)),esk3_0,k1_xboole_0),esk1_1(k9_relat_1(k1_xboole_0,esk3_0))),k4_tarski(esk2_3(esk1_1(k9_relat_1(k1_xboole_0,esk3_0)),esk3_0,k1_xboole_0),esk1_1(k9_relat_1(k1_xboole_0,esk3_0)))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_68,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:29:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.72/0.91  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.72/0.91  # and selection function SelectNegativeLiterals.
% 0.72/0.91  #
% 0.72/0.91  # Preprocessing time       : 0.041 s
% 0.72/0.91  # Presaturation interreduction done
% 0.72/0.91  
% 0.72/0.91  # Proof found!
% 0.72/0.91  # SZS status Theorem
% 0.72/0.91  # SZS output start CNFRefutation
% 0.72/0.91  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.72/0.91  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.72/0.91  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.72/0.91  fof(t150_relat_1, conjecture, ![X1]:k9_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 0.72/0.91  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.72/0.91  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 0.72/0.91  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 0.72/0.91  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.72/0.91  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.72/0.91  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.72/0.91  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.72/0.91  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.72/0.91  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.72/0.91  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.72/0.91  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.72/0.91  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.72/0.91  fof(t19_zfmisc_1, axiom, ![X1, X2]:k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 0.72/0.91  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.72/0.91  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.72/0.91  fof(c_0_19, plain, ![X48, X49]:k1_setfam_1(k2_tarski(X48,X49))=k3_xboole_0(X48,X49), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.72/0.91  fof(c_0_20, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.72/0.91  fof(c_0_21, plain, ![X50]:v1_relat_1(k6_relat_1(X50)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.72/0.91  fof(c_0_22, negated_conjecture, ~(![X1]:k9_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(assume_negation,[status(cth)],[t150_relat_1])).
% 0.72/0.91  fof(c_0_23, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.72/0.91  cnf(c_0_24, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.72/0.91  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.72/0.91  fof(c_0_26, plain, ![X51, X52, X53, X55]:((((r2_hidden(esk2_3(X51,X52,X53),k1_relat_1(X53))|~r2_hidden(X51,k9_relat_1(X53,X52))|~v1_relat_1(X53))&(r2_hidden(k4_tarski(esk2_3(X51,X52,X53),X51),X53)|~r2_hidden(X51,k9_relat_1(X53,X52))|~v1_relat_1(X53)))&(r2_hidden(esk2_3(X51,X52,X53),X52)|~r2_hidden(X51,k9_relat_1(X53,X52))|~v1_relat_1(X53)))&(~r2_hidden(X55,k1_relat_1(X53))|~r2_hidden(k4_tarski(X55,X51),X53)|~r2_hidden(X55,X52)|r2_hidden(X51,k9_relat_1(X53,X52))|~v1_relat_1(X53))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.72/0.91  cnf(c_0_27, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.72/0.91  cnf(c_0_28, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.72/0.91  fof(c_0_29, negated_conjecture, k9_relat_1(k1_xboole_0,esk3_0)!=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 0.72/0.91  fof(c_0_30, plain, ![X8]:(X8=k1_xboole_0|r2_hidden(esk1_1(X8),X8)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.72/0.91  fof(c_0_31, plain, ![X46, X47]:((k4_xboole_0(k1_tarski(X46),k1_tarski(X47))!=k1_tarski(X46)|X46!=X47)&(X46=X47|k4_xboole_0(k1_tarski(X46),k1_tarski(X47))=k1_tarski(X46))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 0.72/0.91  fof(c_0_32, plain, ![X14]:k2_tarski(X14,X14)=k1_tarski(X14), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.72/0.91  cnf(c_0_33, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.72/0.91  cnf(c_0_34, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.72/0.91  fof(c_0_35, plain, ![X17, X18, X19]:k2_enumset1(X17,X17,X18,X19)=k1_enumset1(X17,X18,X19), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.72/0.91  fof(c_0_36, plain, ![X20, X21, X22, X23]:k3_enumset1(X20,X20,X21,X22,X23)=k2_enumset1(X20,X21,X22,X23), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.72/0.91  fof(c_0_37, plain, ![X24, X25, X26, X27, X28]:k4_enumset1(X24,X24,X25,X26,X27,X28)=k3_enumset1(X24,X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.72/0.91  fof(c_0_38, plain, ![X29, X30, X31, X32, X33, X34]:k5_enumset1(X29,X29,X30,X31,X32,X33,X34)=k4_enumset1(X29,X30,X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.72/0.91  fof(c_0_39, plain, ![X35, X36, X37, X38, X39, X40, X41]:k6_enumset1(X35,X35,X36,X37,X38,X39,X40,X41)=k5_enumset1(X35,X36,X37,X38,X39,X40,X41), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.72/0.91  fof(c_0_40, plain, ![X42, X43]:((~r1_tarski(k1_tarski(X42),X43)|r2_hidden(X42,X43))&(~r2_hidden(X42,X43)|r1_tarski(k1_tarski(X42),X43))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.72/0.91  cnf(c_0_41, plain, (r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.72/0.91  cnf(c_0_42, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.72/0.91  cnf(c_0_43, negated_conjecture, (k9_relat_1(k1_xboole_0,esk3_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.72/0.91  cnf(c_0_44, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.72/0.91  cnf(c_0_45, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.72/0.91  cnf(c_0_46, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.72/0.91  cnf(c_0_47, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.72/0.91  cnf(c_0_48, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.72/0.91  cnf(c_0_49, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.72/0.91  cnf(c_0_50, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.72/0.91  cnf(c_0_51, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.72/0.91  cnf(c_0_52, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.72/0.91  fof(c_0_53, plain, ![X44, X45]:k3_xboole_0(k1_tarski(X44),k2_tarski(X44,X45))=k1_tarski(X44), inference(variable_rename,[status(thm)],[t19_zfmisc_1])).
% 0.72/0.91  cnf(c_0_54, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.72/0.91  cnf(c_0_55, plain, (r2_hidden(k4_tarski(esk2_3(X1,X2,k1_xboole_0),X1),k1_xboole_0)|~r2_hidden(X1,k9_relat_1(k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.72/0.91  cnf(c_0_56, negated_conjecture, (r2_hidden(esk1_1(k9_relat_1(k1_xboole_0,esk3_0)),k9_relat_1(k1_xboole_0,esk3_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.72/0.91  cnf(c_0_57, plain, (X1!=X2|k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))!=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_46]), c_0_46]), c_0_25]), c_0_25]), c_0_25]), c_0_47]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52])).
% 0.72/0.91  cnf(c_0_58, plain, (k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.72/0.91  fof(c_0_59, plain, ![X13]:k5_xboole_0(X13,X13)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.72/0.91  fof(c_0_60, plain, ![X12]:(~r1_tarski(X12,k1_xboole_0)|X12=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.72/0.91  cnf(c_0_61, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_46]), c_0_25]), c_0_48]), c_0_49]), c_0_50]), c_0_51]), c_0_52])).
% 0.72/0.91  cnf(c_0_62, negated_conjecture, (r2_hidden(k4_tarski(esk2_3(esk1_1(k9_relat_1(k1_xboole_0,esk3_0)),esk3_0,k1_xboole_0),esk1_1(k9_relat_1(k1_xboole_0,esk3_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.72/0.91  cnf(c_0_63, plain, (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))!=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)), inference(er,[status(thm)],[c_0_57])).
% 0.72/0.91  cnf(c_0_64, plain, (k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_46]), c_0_46]), c_0_25]), c_0_25]), c_0_25]), c_0_34]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52])).
% 0.72/0.91  cnf(c_0_65, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.72/0.91  cnf(c_0_66, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.72/0.91  cnf(c_0_67, negated_conjecture, (r1_tarski(k6_enumset1(k4_tarski(esk2_3(esk1_1(k9_relat_1(k1_xboole_0,esk3_0)),esk3_0,k1_xboole_0),esk1_1(k9_relat_1(k1_xboole_0,esk3_0))),k4_tarski(esk2_3(esk1_1(k9_relat_1(k1_xboole_0,esk3_0)),esk3_0,k1_xboole_0),esk1_1(k9_relat_1(k1_xboole_0,esk3_0))),k4_tarski(esk2_3(esk1_1(k9_relat_1(k1_xboole_0,esk3_0)),esk3_0,k1_xboole_0),esk1_1(k9_relat_1(k1_xboole_0,esk3_0))),k4_tarski(esk2_3(esk1_1(k9_relat_1(k1_xboole_0,esk3_0)),esk3_0,k1_xboole_0),esk1_1(k9_relat_1(k1_xboole_0,esk3_0))),k4_tarski(esk2_3(esk1_1(k9_relat_1(k1_xboole_0,esk3_0)),esk3_0,k1_xboole_0),esk1_1(k9_relat_1(k1_xboole_0,esk3_0))),k4_tarski(esk2_3(esk1_1(k9_relat_1(k1_xboole_0,esk3_0)),esk3_0,k1_xboole_0),esk1_1(k9_relat_1(k1_xboole_0,esk3_0))),k4_tarski(esk2_3(esk1_1(k9_relat_1(k1_xboole_0,esk3_0)),esk3_0,k1_xboole_0),esk1_1(k9_relat_1(k1_xboole_0,esk3_0))),k4_tarski(esk2_3(esk1_1(k9_relat_1(k1_xboole_0,esk3_0)),esk3_0,k1_xboole_0),esk1_1(k9_relat_1(k1_xboole_0,esk3_0)))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.72/0.91  cnf(c_0_68, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64]), c_0_65])).
% 0.72/0.91  cnf(c_0_69, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68]), ['proof']).
% 0.72/0.91  # SZS output end CNFRefutation
% 0.72/0.91  # Proof object total steps             : 70
% 0.72/0.91  # Proof object clause steps            : 32
% 0.72/0.91  # Proof object formula steps           : 38
% 0.72/0.91  # Proof object conjectures             : 8
% 0.72/0.91  # Proof object clause conjectures      : 5
% 0.72/0.91  # Proof object formula conjectures     : 3
% 0.72/0.91  # Proof object initial clauses used    : 19
% 0.72/0.91  # Proof object initial formulas used   : 19
% 0.72/0.91  # Proof object generating inferences   : 6
% 0.72/0.91  # Proof object simplifying inferences  : 101
% 0.72/0.91  # Training examples: 0 positive, 0 negative
% 0.72/0.91  # Parsed axioms                        : 19
% 0.72/0.91  # Removed by relevancy pruning/SinE    : 0
% 0.72/0.91  # Initial clauses                      : 24
% 0.72/0.91  # Removed in clause preprocessing      : 9
% 0.72/0.91  # Initial clauses in saturation        : 15
% 0.72/0.91  # Processed clauses                    : 1535
% 0.72/0.91  # ...of these trivial                  : 132
% 0.72/0.91  # ...subsumed                          : 1028
% 0.72/0.91  # ...remaining for further processing  : 375
% 0.72/0.91  # Other redundant clauses eliminated   : 49
% 0.72/0.91  # Clauses deleted for lack of memory   : 0
% 0.72/0.91  # Backward-subsumed                    : 1
% 0.72/0.91  # Backward-rewritten                   : 29
% 0.72/0.91  # Generated clauses                    : 24807
% 0.72/0.91  # ...of the previous two non-trivial   : 21984
% 0.72/0.91  # Contextual simplify-reflections      : 1
% 0.72/0.91  # Paramodulations                      : 24716
% 0.72/0.91  # Factorizations                       : 42
% 0.72/0.91  # Equation resolutions                 : 49
% 0.72/0.91  # Propositional unsat checks           : 0
% 0.72/0.91  #    Propositional check models        : 0
% 0.72/0.91  #    Propositional check unsatisfiable : 0
% 0.72/0.91  #    Propositional clauses             : 0
% 0.72/0.91  #    Propositional clauses after purity: 0
% 0.72/0.91  #    Propositional unsat core size     : 0
% 0.72/0.91  #    Propositional preprocessing time  : 0.000
% 0.72/0.91  #    Propositional encoding time       : 0.000
% 0.72/0.91  #    Propositional solver time         : 0.000
% 0.72/0.91  #    Success case prop preproc time    : 0.000
% 0.72/0.91  #    Success case prop encoding time   : 0.000
% 0.72/0.91  #    Success case prop solver time     : 0.000
% 0.72/0.91  # Current number of processed clauses  : 329
% 0.72/0.91  #    Positive orientable unit clauses  : 19
% 0.72/0.91  #    Positive unorientable unit clauses: 0
% 0.72/0.91  #    Negative unit clauses             : 2
% 0.72/0.91  #    Non-unit-clauses                  : 308
% 0.72/0.91  # Current number of unprocessed clauses: 20131
% 0.72/0.91  # ...number of literals in the above   : 110328
% 0.72/0.91  # Current number of archived formulas  : 0
% 0.72/0.91  # Current number of archived clauses   : 54
% 0.72/0.91  # Clause-clause subsumption calls (NU) : 26028
% 0.72/0.91  # Rec. Clause-clause subsumption calls : 4411
% 0.72/0.91  # Non-unit clause-clause subsumptions  : 1029
% 0.72/0.91  # Unit Clause-clause subsumption calls : 50
% 0.72/0.91  # Rewrite failures with RHS unbound    : 0
% 0.72/0.91  # BW rewrite match attempts            : 7
% 0.72/0.91  # BW rewrite match successes           : 3
% 0.72/0.91  # Condensation attempts                : 0
% 0.72/0.91  # Condensation successes               : 0
% 0.72/0.91  # Termbank termtop insertions          : 1763514
% 0.72/0.91  
% 0.72/0.91  # -------------------------------------------------
% 0.72/0.91  # User time                : 0.534 s
% 0.72/0.91  # System time              : 0.018 s
% 0.72/0.91  # Total time               : 0.552 s
% 0.72/0.91  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
