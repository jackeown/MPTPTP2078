%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:46 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 220 expanded)
%              Number of clauses        :   30 (  89 expanded)
%              Number of leaves         :   15 (  64 expanded)
%              Depth                    :    8
%              Number of atoms          :   99 ( 289 expanded)
%              Number of equality atoms :   37 ( 180 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t176_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => r1_tarski(k10_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t175_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

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

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => r1_tarski(k10_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))) ) ),
    inference(assume_negation,[status(cth)],[t176_relat_1])).

fof(c_0_16,plain,(
    ! [X49,X50] : k1_setfam_1(k2_tarski(X49,X50)) = k3_xboole_0(X49,X50) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_17,plain,(
    ! [X22,X23] : k1_enumset1(X22,X22,X23) = k2_tarski(X22,X23) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(k2_xboole_0(X12,X13),X14)
      | r1_tarski(X12,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_19,plain,(
    ! [X51,X52,X53] :
      ( ~ v1_relat_1(X53)
      | k10_relat_1(X53,k2_xboole_0(X51,X52)) = k2_xboole_0(k10_relat_1(X53,X51),k10_relat_1(X53,X52)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).

fof(c_0_20,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & ~ r1_tarski(k10_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_21,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X24,X25,X26] : k2_enumset1(X24,X24,X25,X26) = k1_enumset1(X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X27,X28,X29,X30] : k3_enumset1(X27,X27,X28,X29,X30) = k2_enumset1(X27,X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_25,plain,(
    ! [X31,X32,X33,X34,X35] : k4_enumset1(X31,X31,X32,X33,X34,X35) = k3_enumset1(X31,X32,X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_26,plain,(
    ! [X36,X37,X38,X39,X40,X41] : k5_enumset1(X36,X36,X37,X38,X39,X40,X41) = k4_enumset1(X36,X37,X38,X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_27,plain,(
    ! [X42,X43,X44,X45,X46,X47,X48] : k6_enumset1(X42,X42,X43,X44,X45,X46,X47,X48) = k5_enumset1(X42,X43,X44,X45,X46,X47,X48) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_28,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_tarski(X19,X20)
      | ~ r1_tarski(X19,X21)
      | r1_tarski(X19,k3_xboole_0(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( k10_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_31,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k2_xboole_0(X15,X16) = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_32,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_33,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_35,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( r1_tarski(k10_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k10_relat_1(X1,k2_xboole_0(X2,X4)),X3) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_42,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk3_0,k1_setfam_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k1_setfam_1(k6_enumset1(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_46,plain,
    ( r1_tarski(k10_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k10_relat_1(X1,X4),X3)
    | ~ r1_tarski(X2,X4) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_43])).

fof(c_0_48,plain,(
    ! [X17,X18] : r1_tarski(k3_xboole_0(X17,X18),X17) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_49,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk3_0,k1_setfam_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k10_relat_1(esk3_0,esk2_0))
    | ~ r1_tarski(k10_relat_1(esk3_0,k1_setfam_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k10_relat_1(esk3_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_53,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk3_0,k1_setfam_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k10_relat_1(esk3_0,esk1_0))
    | ~ r1_tarski(k1_setfam_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])])).

cnf(c_0_56,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_57,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_51]),c_0_52]),c_0_56])])).

cnf(c_0_59,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:14:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.027 s
% 0.14/0.39  # Presaturation interreduction done
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t176_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k10_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_relat_1)).
% 0.14/0.39  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.14/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.39  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.14/0.39  fof(t175_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 0.14/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.14/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.14/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.14/0.39  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.14/0.39  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.14/0.39  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.14/0.39  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.14/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.14/0.39  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.14/0.39  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.14/0.39  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k10_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))))), inference(assume_negation,[status(cth)],[t176_relat_1])).
% 0.14/0.39  fof(c_0_16, plain, ![X49, X50]:k1_setfam_1(k2_tarski(X49,X50))=k3_xboole_0(X49,X50), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.14/0.39  fof(c_0_17, plain, ![X22, X23]:k1_enumset1(X22,X22,X23)=k2_tarski(X22,X23), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.39  fof(c_0_18, plain, ![X12, X13, X14]:(~r1_tarski(k2_xboole_0(X12,X13),X14)|r1_tarski(X12,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.14/0.39  fof(c_0_19, plain, ![X51, X52, X53]:(~v1_relat_1(X53)|k10_relat_1(X53,k2_xboole_0(X51,X52))=k2_xboole_0(k10_relat_1(X53,X51),k10_relat_1(X53,X52))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).
% 0.14/0.39  fof(c_0_20, negated_conjecture, (v1_relat_1(esk3_0)&~r1_tarski(k10_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.14/0.39  cnf(c_0_21, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.39  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.39  fof(c_0_23, plain, ![X24, X25, X26]:k2_enumset1(X24,X24,X25,X26)=k1_enumset1(X24,X25,X26), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.14/0.39  fof(c_0_24, plain, ![X27, X28, X29, X30]:k3_enumset1(X27,X27,X28,X29,X30)=k2_enumset1(X27,X28,X29,X30), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.14/0.39  fof(c_0_25, plain, ![X31, X32, X33, X34, X35]:k4_enumset1(X31,X31,X32,X33,X34,X35)=k3_enumset1(X31,X32,X33,X34,X35), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.14/0.39  fof(c_0_26, plain, ![X36, X37, X38, X39, X40, X41]:k5_enumset1(X36,X36,X37,X38,X39,X40,X41)=k4_enumset1(X36,X37,X38,X39,X40,X41), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.14/0.39  fof(c_0_27, plain, ![X42, X43, X44, X45, X46, X47, X48]:k6_enumset1(X42,X42,X43,X44,X45,X46,X47,X48)=k5_enumset1(X42,X43,X44,X45,X46,X47,X48), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.14/0.39  fof(c_0_28, plain, ![X19, X20, X21]:(~r1_tarski(X19,X20)|~r1_tarski(X19,X21)|r1_tarski(X19,k3_xboole_0(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.14/0.39  cnf(c_0_29, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.39  cnf(c_0_30, plain, (k10_relat_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.39  fof(c_0_31, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k2_xboole_0(X15,X16)=X16), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.14/0.39  fof(c_0_32, plain, ![X10, X11]:(((r1_tarski(X10,X11)|X10!=X11)&(r1_tarski(X11,X10)|X10!=X11))&(~r1_tarski(X10,X11)|~r1_tarski(X11,X10)|X10=X11)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.14/0.39  cnf(c_0_33, negated_conjecture, (~r1_tarski(k10_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.39  cnf(c_0_34, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.14/0.39  cnf(c_0_35, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.39  cnf(c_0_36, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.39  cnf(c_0_37, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.39  cnf(c_0_38, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.39  cnf(c_0_39, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.39  cnf(c_0_40, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.39  cnf(c_0_41, plain, (r1_tarski(k10_relat_1(X1,X2),X3)|~v1_relat_1(X1)|~r1_tarski(k10_relat_1(X1,k2_xboole_0(X2,X4)),X3)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.14/0.39  cnf(c_0_42, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.39  cnf(c_0_43, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.39  cnf(c_0_44, negated_conjecture, (~r1_tarski(k10_relat_1(esk3_0,k1_setfam_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k1_setfam_1(k6_enumset1(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 0.14/0.39  cnf(c_0_45, plain, (r1_tarski(X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.14/0.39  cnf(c_0_46, plain, (r1_tarski(k10_relat_1(X1,X2),X3)|~v1_relat_1(X1)|~r1_tarski(k10_relat_1(X1,X4),X3)|~r1_tarski(X2,X4)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.14/0.39  cnf(c_0_47, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_43])).
% 0.14/0.39  fof(c_0_48, plain, ![X17, X18]:r1_tarski(k3_xboole_0(X17,X18),X17), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.14/0.39  fof(c_0_49, plain, ![X8, X9]:k3_xboole_0(X8,X9)=k3_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.14/0.39  cnf(c_0_50, negated_conjecture, (~r1_tarski(k10_relat_1(esk3_0,k1_setfam_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k10_relat_1(esk3_0,esk2_0))|~r1_tarski(k10_relat_1(esk3_0,k1_setfam_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k10_relat_1(esk3_0,esk1_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.14/0.39  cnf(c_0_51, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.14/0.39  cnf(c_0_52, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.39  cnf(c_0_53, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.14/0.39  cnf(c_0_54, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.14/0.39  cnf(c_0_55, negated_conjecture, (~r1_tarski(k10_relat_1(esk3_0,k1_setfam_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k10_relat_1(esk3_0,esk1_0))|~r1_tarski(k1_setfam_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])])).
% 0.14/0.39  cnf(c_0_56, plain, (r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.14/0.39  cnf(c_0_57, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 0.14/0.39  cnf(c_0_58, negated_conjecture, (~r1_tarski(k1_setfam_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_51]), c_0_52]), c_0_56])])).
% 0.14/0.39  cnf(c_0_59, plain, (r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X2)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.14/0.39  cnf(c_0_60, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59])]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 61
% 0.14/0.39  # Proof object clause steps            : 30
% 0.14/0.39  # Proof object formula steps           : 31
% 0.14/0.39  # Proof object conjectures             : 10
% 0.14/0.39  # Proof object clause conjectures      : 7
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 16
% 0.14/0.39  # Proof object initial formulas used   : 15
% 0.14/0.39  # Proof object generating inferences   : 7
% 0.14/0.39  # Proof object simplifying inferences  : 45
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 15
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 18
% 0.14/0.39  # Removed in clause preprocessing      : 7
% 0.14/0.39  # Initial clauses in saturation        : 11
% 0.14/0.39  # Processed clauses                    : 149
% 0.14/0.39  # ...of these trivial                  : 2
% 0.14/0.39  # ...subsumed                          : 68
% 0.14/0.39  # ...remaining for further processing  : 79
% 0.14/0.39  # Other redundant clauses eliminated   : 2
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 0
% 0.14/0.39  # Backward-rewritten                   : 2
% 0.14/0.39  # Generated clauses                    : 520
% 0.14/0.39  # ...of the previous two non-trivial   : 482
% 0.14/0.39  # Contextual simplify-reflections      : 0
% 0.14/0.39  # Paramodulations                      : 518
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 2
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 65
% 0.14/0.39  #    Positive orientable unit clauses  : 7
% 0.14/0.39  #    Positive unorientable unit clauses: 1
% 0.14/0.39  #    Negative unit clauses             : 1
% 0.14/0.39  #    Non-unit-clauses                  : 56
% 0.14/0.39  # Current number of unprocessed clauses: 354
% 0.14/0.39  # ...number of literals in the above   : 1144
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 19
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 803
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 733
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 68
% 0.14/0.39  # Unit Clause-clause subsumption calls : 7
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 24
% 0.14/0.39  # BW rewrite match successes           : 17
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 7278
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.039 s
% 0.14/0.39  # System time              : 0.004 s
% 0.14/0.39  # Total time               : 0.043 s
% 0.14/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
