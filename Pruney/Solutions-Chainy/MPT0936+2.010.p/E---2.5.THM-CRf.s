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
% DateTime   : Thu Dec  3 11:00:38 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 352 expanded)
%              Number of clauses        :   24 ( 129 expanded)
%              Number of leaves         :   13 ( 113 expanded)
%              Depth                    :   11
%              Number of atoms          :   70 ( 386 expanded)
%              Number of equality atoms :   62 ( 360 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t97_mcart_1,conjecture,(
    ! [X1,X2,X3] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X1,X2,X3)))) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_mcart_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

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

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(fc3_xboole_0,axiom,(
    ! [X1,X2] : ~ v1_xboole_0(k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).

fof(t195_relat_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
            & k2_relat_1(k2_zfmisc_1(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X1,X2,X3)))) = k1_tarski(X1) ),
    inference(assume_negation,[status(cth)],[t97_mcart_1])).

fof(c_0_14,negated_conjecture,(
    k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(esk1_0,esk2_0,esk3_0)))) != k1_tarski(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_15,plain,(
    ! [X8] : k2_tarski(X8,X8) = k1_tarski(X8) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_16,plain,(
    ! [X9,X10] : k1_enumset1(X9,X9,X10) = k2_tarski(X9,X10) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X11,X12,X13] : k2_enumset1(X11,X11,X12,X13) = k1_enumset1(X11,X12,X13) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_18,plain,(
    ! [X43,X44,X45] : k3_mcart_1(X43,X44,X45) = k4_tarski(k4_tarski(X43,X44),X45) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_19,plain,(
    ! [X14,X15,X16,X17] : k3_enumset1(X14,X14,X15,X16,X17) = k2_enumset1(X14,X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_20,plain,(
    ! [X18,X19,X20,X21,X22] : k4_enumset1(X18,X18,X19,X20,X21,X22) = k3_enumset1(X18,X19,X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_21,plain,(
    ! [X23,X24,X25,X26,X27,X28] : k5_enumset1(X23,X23,X24,X25,X26,X27,X28) = k4_enumset1(X23,X24,X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_22,plain,(
    ! [X29,X30,X31,X32,X33,X34,X35] : k6_enumset1(X29,X29,X30,X31,X32,X33,X34,X35) = k5_enumset1(X29,X30,X31,X32,X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_23,plain,(
    ! [X38,X39,X40] :
      ( k2_zfmisc_1(k1_tarski(X38),k2_tarski(X39,X40)) = k2_tarski(k4_tarski(X38,X39),k4_tarski(X38,X40))
      & k2_zfmisc_1(k2_tarski(X38,X39),k1_tarski(X40)) = k2_tarski(k4_tarski(X38,X40),k4_tarski(X39,X40)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

cnf(c_0_24,negated_conjecture,
    ( k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(esk1_0,esk2_0,esk3_0)))) != k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_34,plain,(
    ! [X36,X37] : ~ v1_xboole_0(k2_tarski(X36,X37)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_xboole_0])])).

cnf(c_0_35,negated_conjecture,
    ( k1_relat_1(k1_relat_1(k6_enumset1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0)))) != k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) = k6_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_27]),c_0_29]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_32])).

fof(c_0_37,plain,(
    ! [X41,X42] :
      ( ( k1_relat_1(k2_zfmisc_1(X41,X42)) = X41
        | X41 = k1_xboole_0
        | X42 = k1_xboole_0 )
      & ( k2_relat_1(k2_zfmisc_1(X41,X42)) = X42
        | X41 = k1_xboole_0
        | X42 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).

cnf(c_0_38,plain,
    ( ~ v1_xboole_0(k2_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) != k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_36])).

cnf(c_0_40,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_41,plain,
    ( ~ v1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_26]),c_0_27]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( k2_zfmisc_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) = k1_xboole_0
    | k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0
    | k1_relat_1(k2_zfmisc_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))) != k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( k2_zfmisc_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) = k1_xboole_0
    | k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) = k1_xboole_0
    | k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) = k1_xboole_0
    | k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_40])).

cnf(c_0_45,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_46,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0
    | k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) = k1_xboole_0
    | k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_47,negated_conjecture,
    ( k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) = k1_xboole_0
    | k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_46]),c_0_45])])).

cnf(c_0_48,negated_conjecture,
    ( k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_47]),c_0_45])])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_48]),c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:41:56 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.13/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.36  #
% 0.13/0.36  # Preprocessing time       : 0.027 s
% 0.13/0.36  # Presaturation interreduction done
% 0.13/0.36  
% 0.13/0.36  # Proof found!
% 0.13/0.36  # SZS status Theorem
% 0.13/0.36  # SZS output start CNFRefutation
% 0.13/0.36  fof(t97_mcart_1, conjecture, ![X1, X2, X3]:k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X1,X2,X3))))=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_mcart_1)).
% 0.13/0.36  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.36  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.36  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.36  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.13/0.36  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.36  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.36  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.13/0.36  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.13/0.36  fof(t36_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))&k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 0.13/0.36  fof(fc3_xboole_0, axiom, ![X1, X2]:~(v1_xboole_0(k2_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_xboole_0)).
% 0.13/0.36  fof(t195_relat_1, axiom, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~((k1_relat_1(k2_zfmisc_1(X1,X2))=X1&k2_relat_1(k2_zfmisc_1(X1,X2))=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 0.13/0.36  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.13/0.36  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X1,X2,X3))))=k1_tarski(X1)), inference(assume_negation,[status(cth)],[t97_mcart_1])).
% 0.13/0.36  fof(c_0_14, negated_conjecture, k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(esk1_0,esk2_0,esk3_0))))!=k1_tarski(esk1_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.13/0.36  fof(c_0_15, plain, ![X8]:k2_tarski(X8,X8)=k1_tarski(X8), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.36  fof(c_0_16, plain, ![X9, X10]:k1_enumset1(X9,X9,X10)=k2_tarski(X9,X10), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.36  fof(c_0_17, plain, ![X11, X12, X13]:k2_enumset1(X11,X11,X12,X13)=k1_enumset1(X11,X12,X13), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.36  fof(c_0_18, plain, ![X43, X44, X45]:k3_mcart_1(X43,X44,X45)=k4_tarski(k4_tarski(X43,X44),X45), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.13/0.36  fof(c_0_19, plain, ![X14, X15, X16, X17]:k3_enumset1(X14,X14,X15,X16,X17)=k2_enumset1(X14,X15,X16,X17), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.36  fof(c_0_20, plain, ![X18, X19, X20, X21, X22]:k4_enumset1(X18,X18,X19,X20,X21,X22)=k3_enumset1(X18,X19,X20,X21,X22), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.36  fof(c_0_21, plain, ![X23, X24, X25, X26, X27, X28]:k5_enumset1(X23,X23,X24,X25,X26,X27,X28)=k4_enumset1(X23,X24,X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.13/0.36  fof(c_0_22, plain, ![X29, X30, X31, X32, X33, X34, X35]:k6_enumset1(X29,X29,X30,X31,X32,X33,X34,X35)=k5_enumset1(X29,X30,X31,X32,X33,X34,X35), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.13/0.36  fof(c_0_23, plain, ![X38, X39, X40]:(k2_zfmisc_1(k1_tarski(X38),k2_tarski(X39,X40))=k2_tarski(k4_tarski(X38,X39),k4_tarski(X38,X40))&k2_zfmisc_1(k2_tarski(X38,X39),k1_tarski(X40))=k2_tarski(k4_tarski(X38,X40),k4_tarski(X39,X40))), inference(variable_rename,[status(thm)],[t36_zfmisc_1])).
% 0.13/0.36  cnf(c_0_24, negated_conjecture, (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(esk1_0,esk2_0,esk3_0))))!=k1_tarski(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.36  cnf(c_0_25, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.36  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.36  cnf(c_0_27, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.36  cnf(c_0_28, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.36  cnf(c_0_29, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.36  cnf(c_0_30, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.36  cnf(c_0_31, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.36  cnf(c_0_32, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.36  cnf(c_0_33, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.36  fof(c_0_34, plain, ![X36, X37]:~v1_xboole_0(k2_tarski(X36,X37)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_xboole_0])])).
% 0.13/0.36  cnf(c_0_35, negated_conjecture, (k1_relat_1(k1_relat_1(k6_enumset1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0))))!=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_32]), c_0_32])).
% 0.13/0.36  cnf(c_0_36, plain, (k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))=k6_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_27]), c_0_29]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_32])).
% 0.13/0.36  fof(c_0_37, plain, ![X41, X42]:((k1_relat_1(k2_zfmisc_1(X41,X42))=X41|(X41=k1_xboole_0|X42=k1_xboole_0))&(k2_relat_1(k2_zfmisc_1(X41,X42))=X42|(X41=k1_xboole_0|X42=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).
% 0.13/0.36  cnf(c_0_38, plain, (~v1_xboole_0(k2_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.36  cnf(c_0_39, negated_conjecture, (k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))!=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_36])).
% 0.13/0.36  cnf(c_0_40, plain, (k1_relat_1(k2_zfmisc_1(X1,X2))=X1|X1=k1_xboole_0|X2=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.36  cnf(c_0_41, plain, (~v1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_26]), c_0_27]), c_0_29]), c_0_30]), c_0_31]), c_0_32])).
% 0.13/0.36  cnf(c_0_42, negated_conjecture, (k2_zfmisc_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))=k1_xboole_0|k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0|k1_relat_1(k2_zfmisc_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))!=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.13/0.36  cnf(c_0_43, plain, (~v1_xboole_0(k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)))), inference(spm,[status(thm)],[c_0_41, c_0_36])).
% 0.13/0.36  cnf(c_0_44, negated_conjecture, (k2_zfmisc_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))=k1_xboole_0|k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)=k1_xboole_0|k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)=k1_xboole_0|k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_40])).
% 0.13/0.36  cnf(c_0_45, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.13/0.36  cnf(c_0_46, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0|k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)=k1_xboole_0|k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.13/0.36  cnf(c_0_47, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)=k1_xboole_0|k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_46]), c_0_45])])).
% 0.13/0.36  cnf(c_0_48, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_47]), c_0_45])])).
% 0.13/0.36  cnf(c_0_49, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_48]), c_0_45])]), ['proof']).
% 0.13/0.36  # SZS output end CNFRefutation
% 0.13/0.36  # Proof object total steps             : 50
% 0.13/0.36  # Proof object clause steps            : 24
% 0.13/0.36  # Proof object formula steps           : 26
% 0.13/0.36  # Proof object conjectures             : 12
% 0.13/0.36  # Proof object clause conjectures      : 9
% 0.13/0.36  # Proof object formula conjectures     : 3
% 0.13/0.36  # Proof object initial clauses used    : 13
% 0.13/0.36  # Proof object initial formulas used   : 13
% 0.13/0.36  # Proof object generating inferences   : 7
% 0.13/0.36  # Proof object simplifying inferences  : 53
% 0.13/0.36  # Training examples: 0 positive, 0 negative
% 0.13/0.36  # Parsed axioms                        : 13
% 0.13/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.36  # Initial clauses                      : 15
% 0.13/0.36  # Removed in clause preprocessing      : 8
% 0.13/0.36  # Initial clauses in saturation        : 7
% 0.13/0.36  # Processed clauses                    : 35
% 0.13/0.36  # ...of these trivial                  : 0
% 0.13/0.36  # ...subsumed                          : 4
% 0.13/0.36  # ...remaining for further processing  : 31
% 0.13/0.36  # Other redundant clauses eliminated   : 0
% 0.13/0.36  # Clauses deleted for lack of memory   : 0
% 0.13/0.36  # Backward-subsumed                    : 6
% 0.13/0.36  # Backward-rewritten                   : 5
% 0.13/0.36  # Generated clauses                    : 141
% 0.13/0.36  # ...of the previous two non-trivial   : 131
% 0.13/0.36  # Contextual simplify-reflections      : 0
% 0.13/0.36  # Paramodulations                      : 140
% 0.13/0.36  # Factorizations                       : 1
% 0.13/0.36  # Equation resolutions                 : 0
% 0.13/0.36  # Propositional unsat checks           : 0
% 0.13/0.36  #    Propositional check models        : 0
% 0.13/0.36  #    Propositional check unsatisfiable : 0
% 0.13/0.36  #    Propositional clauses             : 0
% 0.13/0.36  #    Propositional clauses after purity: 0
% 0.13/0.36  #    Propositional unsat core size     : 0
% 0.13/0.36  #    Propositional preprocessing time  : 0.000
% 0.13/0.36  #    Propositional encoding time       : 0.000
% 0.13/0.36  #    Propositional solver time         : 0.000
% 0.13/0.36  #    Success case prop preproc time    : 0.000
% 0.13/0.36  #    Success case prop encoding time   : 0.000
% 0.13/0.36  #    Success case prop solver time     : 0.000
% 0.13/0.36  # Current number of processed clauses  : 13
% 0.13/0.36  #    Positive orientable unit clauses  : 4
% 0.13/0.36  #    Positive unorientable unit clauses: 0
% 0.13/0.36  #    Negative unit clauses             : 7
% 0.13/0.36  #    Non-unit-clauses                  : 2
% 0.13/0.36  # Current number of unprocessed clauses: 108
% 0.13/0.36  # ...number of literals in the above   : 246
% 0.13/0.36  # Current number of archived formulas  : 0
% 0.13/0.36  # Current number of archived clauses   : 26
% 0.13/0.36  # Clause-clause subsumption calls (NU) : 7
% 0.13/0.36  # Rec. Clause-clause subsumption calls : 7
% 0.13/0.36  # Non-unit clause-clause subsumptions  : 4
% 0.13/0.36  # Unit Clause-clause subsumption calls : 6
% 0.13/0.36  # Rewrite failures with RHS unbound    : 0
% 0.13/0.36  # BW rewrite match attempts            : 4
% 0.13/0.36  # BW rewrite match successes           : 2
% 0.13/0.36  # Condensation attempts                : 0
% 0.13/0.36  # Condensation successes               : 0
% 0.13/0.36  # Termbank termtop insertions          : 2779
% 0.13/0.36  
% 0.13/0.36  # -------------------------------------------------
% 0.13/0.36  # User time                : 0.031 s
% 0.13/0.36  # System time              : 0.002 s
% 0.13/0.36  # Total time               : 0.033 s
% 0.13/0.36  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
