%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:38:09 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   54 (1402 expanded)
%              Number of clauses        :   25 ( 492 expanded)
%              Number of leaves         :   14 ( 450 expanded)
%              Depth                    :    7
%              Number of atoms          :   78 (1567 expanded)
%              Number of equality atoms :   58 (1475 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t20_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

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

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(t17_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X1 != X2
     => r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(t16_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),k1_tarski(X2))
        & X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
      <=> X1 != X2 ) ),
    inference(assume_negation,[status(cth)],[t20_zfmisc_1])).

fof(c_0_15,negated_conjecture,
    ( ( k4_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)) != k1_tarski(esk1_0)
      | esk1_0 = esk2_0 )
    & ( k4_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)) = k1_tarski(esk1_0)
      | esk1_0 != esk2_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_16,plain,(
    ! [X15] : k2_tarski(X15,X15) = k1_tarski(X15) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_17,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_19,plain,(
    ! [X18,X19,X20] : k2_enumset1(X18,X18,X19,X20) = k1_enumset1(X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_20,plain,(
    ! [X21,X22,X23,X24] : k3_enumset1(X21,X21,X22,X23,X24) = k2_enumset1(X21,X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_21,plain,(
    ! [X25,X26,X27,X28,X29] : k4_enumset1(X25,X25,X26,X27,X28,X29) = k3_enumset1(X25,X26,X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_22,plain,(
    ! [X30,X31,X32,X33,X34,X35] : k5_enumset1(X30,X30,X31,X32,X33,X34,X35) = k4_enumset1(X30,X31,X32,X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_23,plain,(
    ! [X36,X37,X38,X39,X40,X41,X42] : k6_enumset1(X36,X36,X37,X38,X39,X40,X41,X42) = k5_enumset1(X36,X37,X38,X39,X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_24,plain,(
    ! [X13,X14] : r1_xboole_0(k4_xboole_0(X13,X14),X14) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_25,negated_conjecture,
    ( esk1_0 = esk2_0
    | k4_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)) != k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_34,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_35,plain,(
    ! [X12] : k5_xboole_0(X12,k1_xboole_0) = X12 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_36,plain,(
    ! [X45,X46] :
      ( X45 = X46
      | r1_xboole_0(k1_tarski(X45),k1_tarski(X46)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_zfmisc_1])])).

fof(c_0_37,plain,(
    ! [X43,X44] :
      ( ~ r1_xboole_0(k1_tarski(X43),k1_tarski(X44))
      | X43 != X44 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_zfmisc_1])])).

cnf(c_0_38,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)) = k1_tarski(esk1_0)
    | esk1_0 != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_40,negated_conjecture,
    ( esk2_0 = esk1_0
    | k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))) != k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_27]),c_0_28]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_33]),c_0_33])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( X1 = X2
    | r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),k1_tarski(X2))
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_38,c_0_28])).

cnf(c_0_46,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))) = k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)
    | esk2_0 != esk1_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_26]),c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_27]),c_0_28]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_33]),c_0_33])).

cnf(c_0_47,negated_conjecture,
    ( esk2_0 = esk1_0
    | ~ r1_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

cnf(c_0_48,plain,
    ( X1 = X2
    | r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_49,plain,
    ( X1 != X2
    | ~ r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_50,negated_conjecture,
    ( r1_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))
    | esk2_0 != esk1_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( esk2_0 = esk1_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,plain,
    ( ~ r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51])]),c_0_52]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.09  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.08/0.30  % Computer   : n010.cluster.edu
% 0.08/0.30  % Model      : x86_64 x86_64
% 0.08/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.30  % Memory     : 8042.1875MB
% 0.08/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.30  % CPULimit   : 60
% 0.08/0.30  % WCLimit    : 600
% 0.08/0.30  % DateTime   : Tue Dec  1 13:15:59 EST 2020
% 0.08/0.30  % CPUTime    : 
% 0.08/0.30  # Version: 2.5pre002
% 0.08/0.30  # No SInE strategy applied
% 0.08/0.30  # Trying AutoSched0 for 299 seconds
% 0.15/0.33  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.15/0.33  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.15/0.33  #
% 0.15/0.33  # Preprocessing time       : 0.028 s
% 0.15/0.33  # Presaturation interreduction done
% 0.15/0.33  
% 0.15/0.33  # Proof found!
% 0.15/0.33  # SZS status Theorem
% 0.15/0.33  # SZS output start CNFRefutation
% 0.15/0.33  fof(t20_zfmisc_1, conjecture, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.15/0.33  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.15/0.33  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.15/0.33  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.15/0.33  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.15/0.33  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.15/0.33  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.15/0.33  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.15/0.33  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.15/0.33  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.15/0.33  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.15/0.33  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.15/0.33  fof(t17_zfmisc_1, axiom, ![X1, X2]:(X1!=X2=>r1_xboole_0(k1_tarski(X1),k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 0.15/0.33  fof(t16_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),k1_tarski(X2))&X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 0.15/0.33  fof(c_0_14, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2)), inference(assume_negation,[status(cth)],[t20_zfmisc_1])).
% 0.15/0.33  fof(c_0_15, negated_conjecture, ((k4_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))!=k1_tarski(esk1_0)|esk1_0=esk2_0)&(k4_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))=k1_tarski(esk1_0)|esk1_0!=esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.15/0.33  fof(c_0_16, plain, ![X15]:k2_tarski(X15,X15)=k1_tarski(X15), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.15/0.33  fof(c_0_17, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.15/0.33  fof(c_0_18, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.15/0.33  fof(c_0_19, plain, ![X18, X19, X20]:k2_enumset1(X18,X18,X19,X20)=k1_enumset1(X18,X19,X20), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.15/0.33  fof(c_0_20, plain, ![X21, X22, X23, X24]:k3_enumset1(X21,X21,X22,X23,X24)=k2_enumset1(X21,X22,X23,X24), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.15/0.33  fof(c_0_21, plain, ![X25, X26, X27, X28, X29]:k4_enumset1(X25,X25,X26,X27,X28,X29)=k3_enumset1(X25,X26,X27,X28,X29), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.15/0.33  fof(c_0_22, plain, ![X30, X31, X32, X33, X34, X35]:k5_enumset1(X30,X30,X31,X32,X33,X34,X35)=k4_enumset1(X30,X31,X32,X33,X34,X35), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.15/0.33  fof(c_0_23, plain, ![X36, X37, X38, X39, X40, X41, X42]:k6_enumset1(X36,X36,X37,X38,X39,X40,X41,X42)=k5_enumset1(X36,X37,X38,X39,X40,X41,X42), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.15/0.33  fof(c_0_24, plain, ![X13, X14]:r1_xboole_0(k4_xboole_0(X13,X14),X14), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.15/0.33  cnf(c_0_25, negated_conjecture, (esk1_0=esk2_0|k4_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))!=k1_tarski(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.15/0.33  cnf(c_0_26, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.15/0.33  cnf(c_0_27, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.15/0.33  cnf(c_0_28, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.15/0.33  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.15/0.33  cnf(c_0_30, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.15/0.33  cnf(c_0_31, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.15/0.33  cnf(c_0_32, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.15/0.33  cnf(c_0_33, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.15/0.33  fof(c_0_34, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.15/0.33  fof(c_0_35, plain, ![X12]:k5_xboole_0(X12,k1_xboole_0)=X12, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.15/0.33  fof(c_0_36, plain, ![X45, X46]:(X45=X46|r1_xboole_0(k1_tarski(X45),k1_tarski(X46))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_zfmisc_1])])).
% 0.15/0.33  fof(c_0_37, plain, ![X43, X44]:(~r1_xboole_0(k1_tarski(X43),k1_tarski(X44))|X43!=X44), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_zfmisc_1])])).
% 0.15/0.33  cnf(c_0_38, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.15/0.33  cnf(c_0_39, negated_conjecture, (k4_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))=k1_tarski(esk1_0)|esk1_0!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.15/0.33  cnf(c_0_40, negated_conjecture, (esk2_0=esk1_0|k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))!=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_27]), c_0_28]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_33]), c_0_33])).
% 0.15/0.33  cnf(c_0_41, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.15/0.33  cnf(c_0_42, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.15/0.33  cnf(c_0_43, plain, (X1=X2|r1_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.15/0.33  cnf(c_0_44, plain, (~r1_xboole_0(k1_tarski(X1),k1_tarski(X2))|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.15/0.33  cnf(c_0_45, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_38, c_0_28])).
% 0.15/0.33  cnf(c_0_46, negated_conjecture, (k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)|esk2_0!=esk1_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_26]), c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_27]), c_0_28]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_33]), c_0_33])).
% 0.15/0.33  cnf(c_0_47, negated_conjecture, (esk2_0=esk1_0|~r1_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])])).
% 0.15/0.33  cnf(c_0_48, plain, (X1=X2|r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33])).
% 0.15/0.33  cnf(c_0_49, plain, (X1!=X2|~r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33])).
% 0.15/0.33  cnf(c_0_50, negated_conjecture, (r1_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))|esk2_0!=esk1_0), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.15/0.33  cnf(c_0_51, negated_conjecture, (esk2_0=esk1_0), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.15/0.33  cnf(c_0_52, plain, (~r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))), inference(er,[status(thm)],[c_0_49])).
% 0.15/0.33  cnf(c_0_53, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51])]), c_0_52]), ['proof']).
% 0.15/0.33  # SZS output end CNFRefutation
% 0.15/0.33  # Proof object total steps             : 54
% 0.15/0.33  # Proof object clause steps            : 25
% 0.15/0.33  # Proof object formula steps           : 29
% 0.15/0.33  # Proof object conjectures             : 11
% 0.15/0.33  # Proof object clause conjectures      : 8
% 0.15/0.33  # Proof object formula conjectures     : 3
% 0.15/0.33  # Proof object initial clauses used    : 15
% 0.15/0.33  # Proof object initial formulas used   : 14
% 0.15/0.33  # Proof object generating inferences   : 3
% 0.15/0.33  # Proof object simplifying inferences  : 97
% 0.15/0.33  # Training examples: 0 positive, 0 negative
% 0.15/0.33  # Parsed axioms                        : 14
% 0.15/0.33  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.33  # Initial clauses                      : 16
% 0.15/0.33  # Removed in clause preprocessing      : 8
% 0.15/0.33  # Initial clauses in saturation        : 8
% 0.15/0.33  # Processed clauses                    : 20
% 0.15/0.33  # ...of these trivial                  : 0
% 0.15/0.33  # ...subsumed                          : 0
% 0.15/0.33  # ...remaining for further processing  : 20
% 0.15/0.33  # Other redundant clauses eliminated   : 1
% 0.15/0.33  # Clauses deleted for lack of memory   : 0
% 0.15/0.33  # Backward-subsumed                    : 0
% 0.15/0.33  # Backward-rewritten                   : 4
% 0.15/0.33  # Generated clauses                    : 9
% 0.15/0.33  # ...of the previous two non-trivial   : 5
% 0.15/0.33  # Contextual simplify-reflections      : 0
% 0.15/0.33  # Paramodulations                      : 8
% 0.15/0.33  # Factorizations                       : 0
% 0.15/0.33  # Equation resolutions                 : 1
% 0.15/0.33  # Propositional unsat checks           : 0
% 0.15/0.33  #    Propositional check models        : 0
% 0.15/0.33  #    Propositional check unsatisfiable : 0
% 0.15/0.33  #    Propositional clauses             : 0
% 0.15/0.33  #    Propositional clauses after purity: 0
% 0.15/0.33  #    Propositional unsat core size     : 0
% 0.15/0.33  #    Propositional preprocessing time  : 0.000
% 0.15/0.33  #    Propositional encoding time       : 0.000
% 0.15/0.33  #    Propositional solver time         : 0.000
% 0.15/0.33  #    Success case prop preproc time    : 0.000
% 0.15/0.33  #    Success case prop encoding time   : 0.000
% 0.15/0.33  #    Success case prop solver time     : 0.000
% 0.15/0.33  # Current number of processed clauses  : 7
% 0.15/0.33  #    Positive orientable unit clauses  : 3
% 0.15/0.33  #    Positive unorientable unit clauses: 0
% 0.15/0.33  #    Negative unit clauses             : 1
% 0.15/0.33  #    Non-unit-clauses                  : 3
% 0.15/0.33  # Current number of unprocessed clauses: 0
% 0.15/0.33  # ...number of literals in the above   : 0
% 0.15/0.33  # Current number of archived formulas  : 0
% 0.15/0.33  # Current number of archived clauses   : 20
% 0.15/0.33  # Clause-clause subsumption calls (NU) : 0
% 0.15/0.33  # Rec. Clause-clause subsumption calls : 0
% 0.15/0.33  # Non-unit clause-clause subsumptions  : 0
% 0.15/0.33  # Unit Clause-clause subsumption calls : 1
% 0.15/0.33  # Rewrite failures with RHS unbound    : 0
% 0.15/0.33  # BW rewrite match attempts            : 1
% 0.15/0.33  # BW rewrite match successes           : 1
% 0.15/0.33  # Condensation attempts                : 0
% 0.15/0.33  # Condensation successes               : 0
% 0.15/0.33  # Termbank termtop insertions          : 1090
% 0.15/0.33  
% 0.15/0.33  # -------------------------------------------------
% 0.15/0.33  # User time                : 0.026 s
% 0.15/0.33  # System time              : 0.005 s
% 0.15/0.33  # Total time               : 0.031 s
% 0.15/0.33  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
