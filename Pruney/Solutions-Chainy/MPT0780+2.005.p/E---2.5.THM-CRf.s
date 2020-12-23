%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:49 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 143 expanded)
%              Number of clauses        :   38 (  63 expanded)
%              Number of leaves         :   15 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  151 ( 278 expanded)
%              Number of equality atoms :   41 ( 102 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t29_wellord1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k2_wellord1(k2_wellord1(X3,X2),X1) = k2_wellord1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(t125_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k8_relat_1(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(t19_wellord1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k3_relat_1(k2_wellord1(X3,X2)))
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_wellord1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t17_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(X2,X1) = k7_relat_1(k8_relat_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_wellord1)).

fof(t27_wellord1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k2_wellord1(k2_wellord1(X3,X1),X2) = k2_wellord1(k2_wellord1(X3,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_wellord1)).

fof(dt_k2_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k2_wellord1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(c_0_15,plain,(
    ! [X23,X24] : k3_tarski(k2_tarski(X23,X24)) = k2_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(X1,X2)
         => k2_wellord1(k2_wellord1(X3,X2),X1) = k2_wellord1(X3,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t29_wellord1])).

fof(c_0_18,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(k2_xboole_0(X10,X11),X12)
      | r1_tarski(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_19,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X20,X21,X22] : k2_enumset1(X20,X20,X21,X22) = k1_enumset1(X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_22,plain,(
    ! [X16,X17] : k2_tarski(X16,X17) = k2_tarski(X17,X16) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_23,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X14,X15)
      | r1_tarski(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_24,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & r1_tarski(esk2_0,esk3_0)
    & k2_wellord1(k2_wellord1(esk4_0,esk3_0),esk2_0) != k2_wellord1(esk4_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X25] :
      ( ~ v1_relat_1(X25)
      | k3_relat_1(X25) = k2_xboole_0(k1_relat_1(X25),k2_relat_1(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

fof(c_0_30,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X27)
      | ~ r1_tarski(k2_relat_1(X27),X26)
      | k8_relat_1(X26,X27) = X27 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k3_tarski(k2_enumset1(X1,X1,X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_34,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_enumset1(X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_20]),c_0_20]),c_0_27]),c_0_27])).

cnf(c_0_35,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_36,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X29)
      | ~ r1_tarski(k1_relat_1(X29),X28)
      | k7_relat_1(X29,X28) = X29 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_37,plain,
    ( k8_relat_1(X2,X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k3_tarski(k2_enumset1(X3,X3,X3,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( k3_relat_1(X1) = k3_tarski(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_26]),c_0_27])).

fof(c_0_41,plain,(
    ! [X34,X35,X36] :
      ( ( r2_hidden(X34,k3_relat_1(X36))
        | ~ r2_hidden(X34,k3_relat_1(k2_wellord1(X36,X35)))
        | ~ v1_relat_1(X36) )
      & ( r2_hidden(X34,X35)
        | ~ r2_hidden(X34,k3_relat_1(k2_wellord1(X36,X35)))
        | ~ v1_relat_1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_wellord1])])])).

fof(c_0_42,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_43,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_44,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | k2_wellord1(X33,X32) = k7_relat_1(k8_relat_1(X32,X33),X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_wellord1])])).

cnf(c_0_45,negated_conjecture,
    ( k8_relat_1(esk3_0,X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_46,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k3_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_relat_1(k2_wellord1(X3,X2)))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( k7_relat_1(X1,esk3_0) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_38])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k3_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_40])).

cnf(c_0_51,plain,
    ( k2_wellord1(X1,X2) = k7_relat_1(k8_relat_1(X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( k8_relat_1(esk3_0,X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k3_relat_1(X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,plain,
    ( r2_hidden(esk1_2(k3_relat_1(k2_wellord1(X1,X2)),X3),X2)
    | r1_tarski(k3_relat_1(k2_wellord1(X1,X2)),X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_55,plain,(
    ! [X37,X38,X39] :
      ( ~ v1_relat_1(X39)
      | k2_wellord1(k2_wellord1(X39,X37),X38) = k2_wellord1(k2_wellord1(X39,X38),X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_wellord1])])).

cnf(c_0_56,negated_conjecture,
    ( k7_relat_1(X1,esk3_0) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k3_relat_1(X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( k7_relat_1(X1,esk3_0) = k2_wellord1(X1,esk3_0)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k3_relat_1(X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk1_2(k3_relat_1(k2_wellord1(esk4_0,X1)),X2),X1)
    | r1_tarski(k3_relat_1(k2_wellord1(esk4_0,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( k2_wellord1(k2_wellord1(esk4_0,esk3_0),esk2_0) != k2_wellord1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_61,plain,
    ( k2_wellord1(k2_wellord1(X1,X2),X3) = k2_wellord1(k2_wellord1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( k2_wellord1(X1,esk3_0) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k3_relat_1(X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k3_relat_1(k2_wellord1(esk4_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( k2_wellord1(k2_wellord1(esk4_0,esk2_0),esk3_0) != k2_wellord1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_54])])).

fof(c_0_65,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X30)
      | v1_relat_1(k2_wellord1(X30,X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).

cnf(c_0_66,negated_conjecture,
    ( ~ v1_relat_1(k2_wellord1(esk4_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_67,plain,
    ( v1_relat_1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_54])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:02:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.027 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.20/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.39  fof(t29_wellord1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k2_wellord1(k2_wellord1(X3,X2),X1)=k2_wellord1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_wellord1)).
% 0.20/0.39  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.20/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.39  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.20/0.39  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.20/0.39  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 0.20/0.39  fof(t125_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k8_relat_1(X1,X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 0.20/0.39  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 0.20/0.39  fof(t19_wellord1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k3_relat_1(k2_wellord1(X3,X2)))=>(r2_hidden(X1,k3_relat_1(X3))&r2_hidden(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_wellord1)).
% 0.20/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.39  fof(t17_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_wellord1(X2,X1)=k7_relat_1(k8_relat_1(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_wellord1)).
% 0.20/0.39  fof(t27_wellord1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k2_wellord1(k2_wellord1(X3,X1),X2)=k2_wellord1(k2_wellord1(X3,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_wellord1)).
% 0.20/0.39  fof(dt_k2_wellord1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k2_wellord1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_wellord1)).
% 0.20/0.39  fof(c_0_15, plain, ![X23, X24]:k3_tarski(k2_tarski(X23,X24))=k2_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.20/0.39  fof(c_0_16, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.39  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k2_wellord1(k2_wellord1(X3,X2),X1)=k2_wellord1(X3,X1)))), inference(assume_negation,[status(cth)],[t29_wellord1])).
% 0.20/0.39  fof(c_0_18, plain, ![X10, X11, X12]:(~r1_tarski(k2_xboole_0(X10,X11),X12)|r1_tarski(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.20/0.39  cnf(c_0_19, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  fof(c_0_21, plain, ![X20, X21, X22]:k2_enumset1(X20,X20,X21,X22)=k1_enumset1(X20,X21,X22), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.39  fof(c_0_22, plain, ![X16, X17]:k2_tarski(X16,X17)=k2_tarski(X17,X16), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.20/0.39  fof(c_0_23, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_tarski(X14,X15)|r1_tarski(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.20/0.39  fof(c_0_24, negated_conjecture, (v1_relat_1(esk4_0)&(r1_tarski(esk2_0,esk3_0)&k2_wellord1(k2_wellord1(esk4_0,esk3_0),esk2_0)!=k2_wellord1(esk4_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.20/0.39  cnf(c_0_25, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_26, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.39  cnf(c_0_27, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.39  cnf(c_0_28, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.39  fof(c_0_29, plain, ![X25]:(~v1_relat_1(X25)|k3_relat_1(X25)=k2_xboole_0(k1_relat_1(X25),k2_relat_1(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 0.20/0.39  fof(c_0_30, plain, ![X26, X27]:(~v1_relat_1(X27)|(~r1_tarski(k2_relat_1(X27),X26)|k8_relat_1(X26,X27)=X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).
% 0.20/0.39  cnf(c_0_31, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.39  cnf(c_0_32, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  cnf(c_0_33, plain, (r1_tarski(X1,X3)|~r1_tarski(k3_tarski(k2_enumset1(X1,X1,X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.20/0.39  cnf(c_0_34, plain, (k2_enumset1(X1,X1,X1,X2)=k2_enumset1(X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_20]), c_0_20]), c_0_27]), c_0_27])).
% 0.20/0.39  cnf(c_0_35, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.39  fof(c_0_36, plain, ![X28, X29]:(~v1_relat_1(X29)|(~r1_tarski(k1_relat_1(X29),X28)|k7_relat_1(X29,X28)=X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.20/0.39  cnf(c_0_37, plain, (k8_relat_1(X2,X1)=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.39  cnf(c_0_38, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.39  cnf(c_0_39, plain, (r1_tarski(X1,X2)|~r1_tarski(k3_tarski(k2_enumset1(X3,X3,X3,X1)),X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.39  cnf(c_0_40, plain, (k3_relat_1(X1)=k3_tarski(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_26]), c_0_27])).
% 0.20/0.39  fof(c_0_41, plain, ![X34, X35, X36]:((r2_hidden(X34,k3_relat_1(X36))|~r2_hidden(X34,k3_relat_1(k2_wellord1(X36,X35)))|~v1_relat_1(X36))&(r2_hidden(X34,X35)|~r2_hidden(X34,k3_relat_1(k2_wellord1(X36,X35)))|~v1_relat_1(X36))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_wellord1])])])).
% 0.20/0.39  fof(c_0_42, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.39  cnf(c_0_43, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.39  fof(c_0_44, plain, ![X32, X33]:(~v1_relat_1(X33)|k2_wellord1(X33,X32)=k7_relat_1(k8_relat_1(X32,X33),X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_wellord1])])).
% 0.20/0.39  cnf(c_0_45, negated_conjecture, (k8_relat_1(esk3_0,X1)=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),esk2_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.39  cnf(c_0_46, plain, (r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~r1_tarski(k3_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.39  cnf(c_0_47, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_relat_1(k2_wellord1(X3,X2)))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.39  cnf(c_0_48, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.39  cnf(c_0_49, negated_conjecture, (k7_relat_1(X1,esk3_0)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),esk2_0)), inference(spm,[status(thm)],[c_0_43, c_0_38])).
% 0.20/0.39  cnf(c_0_50, plain, (r1_tarski(k1_relat_1(X1),X2)|~v1_relat_1(X1)|~r1_tarski(k3_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_33, c_0_40])).
% 0.20/0.39  cnf(c_0_51, plain, (k2_wellord1(X1,X2)=k7_relat_1(k8_relat_1(X2,X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.39  cnf(c_0_52, negated_conjecture, (k8_relat_1(esk3_0,X1)=X1|~v1_relat_1(X1)|~r1_tarski(k3_relat_1(X1),esk2_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.39  cnf(c_0_53, plain, (r2_hidden(esk1_2(k3_relat_1(k2_wellord1(X1,X2)),X3),X2)|r1_tarski(k3_relat_1(k2_wellord1(X1,X2)),X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.39  cnf(c_0_54, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  fof(c_0_55, plain, ![X37, X38, X39]:(~v1_relat_1(X39)|k2_wellord1(k2_wellord1(X39,X37),X38)=k2_wellord1(k2_wellord1(X39,X38),X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_wellord1])])).
% 0.20/0.39  cnf(c_0_56, negated_conjecture, (k7_relat_1(X1,esk3_0)=X1|~v1_relat_1(X1)|~r1_tarski(k3_relat_1(X1),esk2_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.39  cnf(c_0_57, negated_conjecture, (k7_relat_1(X1,esk3_0)=k2_wellord1(X1,esk3_0)|~v1_relat_1(X1)|~r1_tarski(k3_relat_1(X1),esk2_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.39  cnf(c_0_58, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.39  cnf(c_0_59, negated_conjecture, (r2_hidden(esk1_2(k3_relat_1(k2_wellord1(esk4_0,X1)),X2),X1)|r1_tarski(k3_relat_1(k2_wellord1(esk4_0,X1)),X2)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.39  cnf(c_0_60, negated_conjecture, (k2_wellord1(k2_wellord1(esk4_0,esk3_0),esk2_0)!=k2_wellord1(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  cnf(c_0_61, plain, (k2_wellord1(k2_wellord1(X1,X2),X3)=k2_wellord1(k2_wellord1(X1,X3),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.39  cnf(c_0_62, negated_conjecture, (k2_wellord1(X1,esk3_0)=X1|~v1_relat_1(X1)|~r1_tarski(k3_relat_1(X1),esk2_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.39  cnf(c_0_63, negated_conjecture, (r1_tarski(k3_relat_1(k2_wellord1(esk4_0,X1)),X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.20/0.39  cnf(c_0_64, negated_conjecture, (k2_wellord1(k2_wellord1(esk4_0,esk2_0),esk3_0)!=k2_wellord1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_54])])).
% 0.20/0.39  fof(c_0_65, plain, ![X30, X31]:(~v1_relat_1(X30)|v1_relat_1(k2_wellord1(X30,X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).
% 0.20/0.39  cnf(c_0_66, negated_conjecture, (~v1_relat_1(k2_wellord1(esk4_0,esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.20/0.39  cnf(c_0_67, plain, (v1_relat_1(k2_wellord1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.20/0.39  cnf(c_0_68, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_54])]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 69
% 0.20/0.39  # Proof object clause steps            : 38
% 0.20/0.39  # Proof object formula steps           : 31
% 0.20/0.39  # Proof object conjectures             : 18
% 0.20/0.39  # Proof object clause conjectures      : 15
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 18
% 0.20/0.39  # Proof object initial formulas used   : 15
% 0.20/0.39  # Proof object generating inferences   : 16
% 0.20/0.39  # Proof object simplifying inferences  : 14
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 15
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 20
% 0.20/0.39  # Removed in clause preprocessing      : 3
% 0.20/0.39  # Initial clauses in saturation        : 17
% 0.20/0.39  # Processed clauses                    : 184
% 0.20/0.39  # ...of these trivial                  : 2
% 0.20/0.39  # ...subsumed                          : 85
% 0.20/0.39  # ...remaining for further processing  : 97
% 0.20/0.39  # Other redundant clauses eliminated   : 0
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 1
% 0.20/0.39  # Backward-rewritten                   : 0
% 0.20/0.39  # Generated clauses                    : 327
% 0.20/0.39  # ...of the previous two non-trivial   : 310
% 0.20/0.39  # Contextual simplify-reflections      : 5
% 0.20/0.39  # Paramodulations                      : 327
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 0
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 79
% 0.20/0.39  #    Positive orientable unit clauses  : 6
% 0.20/0.39  #    Positive unorientable unit clauses: 1
% 0.20/0.39  #    Negative unit clauses             : 3
% 0.20/0.39  #    Non-unit-clauses                  : 69
% 0.20/0.39  # Current number of unprocessed clauses: 160
% 0.20/0.39  # ...number of literals in the above   : 490
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 21
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 788
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 555
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 90
% 0.20/0.39  # Unit Clause-clause subsumption calls : 4
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 7
% 0.20/0.39  # BW rewrite match successes           : 2
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 5914
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.036 s
% 0.20/0.39  # System time              : 0.004 s
% 0.20/0.39  # Total time               : 0.041 s
% 0.20/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
