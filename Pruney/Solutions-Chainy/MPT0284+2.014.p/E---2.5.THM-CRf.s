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
% DateTime   : Thu Dec  3 10:43:13 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 158 expanded)
%              Number of clauses        :   30 (  69 expanded)
%              Number of leaves         :   13 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :   74 ( 184 expanded)
%              Number of equality atoms :   27 ( 117 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t86_zfmisc_1,conjecture,(
    ! [X1,X2] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X1,X2)),k1_zfmisc_1(k4_xboole_0(X2,X1))),k1_zfmisc_1(k5_xboole_0(X1,X2))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_zfmisc_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t110_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k5_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

fof(t108_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(t79_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X1,X2)),k1_zfmisc_1(k4_xboole_0(X2,X1))),k1_zfmisc_1(k5_xboole_0(X1,X2))) ),
    inference(assume_negation,[status(cth)],[t86_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X27,X28] : k3_tarski(k2_tarski(X27,X28)) = k2_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X22,X23] : k1_enumset1(X22,X22,X23) = k2_tarski(X22,X23) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,negated_conjecture,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(esk1_0,esk2_0)),k1_zfmisc_1(k4_xboole_0(esk2_0,esk1_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_17,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_20,plain,(
    ! [X24,X25,X26] : k2_enumset1(X24,X24,X25,X26) = k1_enumset1(X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_21,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(esk1_0,esk2_0)),k1_zfmisc_1(k4_xboole_0(esk2_0,esk1_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_26,plain,(
    ! [X20,X21] : k2_xboole_0(X20,X21) = k5_xboole_0(X20,k4_xboole_0(X21,X20)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_27,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k2_enumset1(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk1_0))))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_23]),c_0_23]),c_0_24])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k2_enumset1(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_22]),c_0_23]),c_0_24])).

fof(c_0_32,plain,(
    ! [X15,X16,X17] :
      ( ~ r1_tarski(X15,X16)
      | ~ r1_tarski(X17,X16)
      | r1_tarski(k5_xboole_0(X15,X17),X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t110_xboole_1])])).

fof(c_0_33,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | r1_tarski(k3_xboole_0(X12,X14),X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).

cnf(c_0_34,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_28])).

cnf(c_0_35,plain,
    ( r1_tarski(k5_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,plain,
    ( r1_tarski(k3_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_37,plain,(
    ! [X18,X19] : r1_tarski(X18,k2_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_38,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

cnf(c_0_39,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0)))
    | ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_28])).

fof(c_0_41,plain,(
    ! [X29,X30] :
      ( ~ r1_tarski(X29,X30)
      | r1_tarski(k1_zfmisc_1(X29),k1_zfmisc_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0)))
    | ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_35]),c_0_40])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,k3_tarski(k2_enumset1(X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_22]),c_0_24])).

cnf(c_0_47,plain,
    ( k5_xboole_0(X1,X2) = k3_tarski(k2_enumset1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_22]),c_0_23]),c_0_23]),c_0_23]),c_0_24])).

fof(c_0_48,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k5_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_49,negated_conjecture,
    ( ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0)))
    | ~ r1_tarski(k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(esk1_0,esk2_0))
    | ~ r1_tarski(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_45])).

cnf(c_0_53,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_50])])).

cnf(c_0_55,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),k5_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_28])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:17:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.026 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t86_zfmisc_1, conjecture, ![X1, X2]:r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X1,X2)),k1_zfmisc_1(k4_xboole_0(X2,X1))),k1_zfmisc_1(k5_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_zfmisc_1)).
% 0.13/0.37  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.13/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.37  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.37  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.13/0.37  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.13/0.37  fof(t110_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k5_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_xboole_1)).
% 0.13/0.37  fof(t108_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k3_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 0.13/0.37  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.13/0.37  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 0.13/0.37  fof(t79_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 0.13/0.37  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.13/0.37  fof(c_0_13, negated_conjecture, ~(![X1, X2]:r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X1,X2)),k1_zfmisc_1(k4_xboole_0(X2,X1))),k1_zfmisc_1(k5_xboole_0(X1,X2)))), inference(assume_negation,[status(cth)],[t86_zfmisc_1])).
% 0.13/0.37  fof(c_0_14, plain, ![X27, X28]:k3_tarski(k2_tarski(X27,X28))=k2_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.13/0.37  fof(c_0_15, plain, ![X22, X23]:k1_enumset1(X22,X22,X23)=k2_tarski(X22,X23), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.37  fof(c_0_16, negated_conjecture, ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(esk1_0,esk2_0)),k1_zfmisc_1(k4_xboole_0(esk2_0,esk1_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.13/0.37  cnf(c_0_17, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  fof(c_0_19, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.37  fof(c_0_20, plain, ![X24, X25, X26]:k2_enumset1(X24,X24,X25,X26)=k1_enumset1(X24,X25,X26), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(esk1_0,esk2_0)),k1_zfmisc_1(k4_xboole_0(esk2_0,esk1_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_22, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.37  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  cnf(c_0_24, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.37  fof(c_0_25, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.13/0.37  fof(c_0_26, plain, ![X20, X21]:k2_xboole_0(X20,X21)=k5_xboole_0(X20,k4_xboole_0(X21,X20)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, (~r1_tarski(k3_tarski(k2_enumset1(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk1_0))))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_23]), c_0_23]), c_0_24])).
% 0.13/0.37  cnf(c_0_28, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.37  cnf(c_0_29, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (~r1_tarski(k3_tarski(k2_enumset1(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0)))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.37  cnf(c_0_31, plain, (k3_tarski(k2_enumset1(X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_22]), c_0_23]), c_0_24])).
% 0.13/0.37  fof(c_0_32, plain, ![X15, X16, X17]:(~r1_tarski(X15,X16)|~r1_tarski(X17,X16)|r1_tarski(k5_xboole_0(X15,X17),X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t110_xboole_1])])).
% 0.13/0.37  fof(c_0_33, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|r1_tarski(k3_xboole_0(X12,X14),X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (~r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_28])).
% 0.13/0.37  cnf(c_0_35, plain, (r1_tarski(k5_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.37  cnf(c_0_36, plain, (r1_tarski(k3_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.37  fof(c_0_37, plain, ![X18, X19]:r1_tarski(X18,k2_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.13/0.37  fof(c_0_38, plain, ![X8, X9]:k5_xboole_0(X8,X9)=k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 0.13/0.37  cnf(c_0_39, negated_conjecture, (~r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0)))|~r1_tarski(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.37  cnf(c_0_40, plain, (r1_tarski(k3_xboole_0(X1,X2),X3)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_36, c_0_28])).
% 0.13/0.37  fof(c_0_41, plain, ![X29, X30]:(~r1_tarski(X29,X30)|r1_tarski(k1_zfmisc_1(X29),k1_zfmisc_1(X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).
% 0.13/0.37  cnf(c_0_42, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.37  cnf(c_0_43, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.37  cnf(c_0_44, negated_conjecture, (~r1_tarski(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0)))|~r1_tarski(k1_zfmisc_1(k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_35]), c_0_40])).
% 0.13/0.37  cnf(c_0_45, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.37  cnf(c_0_46, plain, (r1_tarski(X1,k3_tarski(k2_enumset1(X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_22]), c_0_24])).
% 0.13/0.37  cnf(c_0_47, plain, (k5_xboole_0(X1,X2)=k3_tarski(k2_enumset1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_22]), c_0_23]), c_0_23]), c_0_23]), c_0_24])).
% 0.13/0.37  fof(c_0_48, plain, ![X6, X7]:k5_xboole_0(X6,X7)=k5_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.13/0.37  cnf(c_0_49, negated_conjecture, (~r1_tarski(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0)))|~r1_tarski(k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.13/0.37  cnf(c_0_50, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.13/0.37  cnf(c_0_51, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.13/0.37  cnf(c_0_52, negated_conjecture, (~r1_tarski(k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(esk1_0,esk2_0))|~r1_tarski(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_49, c_0_45])).
% 0.13/0.37  cnf(c_0_53, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.13/0.37  cnf(c_0_54, negated_conjecture, (~r1_tarski(k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_50])])).
% 0.13/0.37  cnf(c_0_55, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),k5_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_53, c_0_28])).
% 0.13/0.37  cnf(c_0_56, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55])]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 57
% 0.13/0.37  # Proof object clause steps            : 30
% 0.13/0.37  # Proof object formula steps           : 27
% 0.13/0.37  # Proof object conjectures             : 13
% 0.13/0.37  # Proof object clause conjectures      : 10
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 13
% 0.13/0.37  # Proof object initial formulas used   : 13
% 0.13/0.37  # Proof object generating inferences   : 8
% 0.13/0.37  # Proof object simplifying inferences  : 24
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 13
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 13
% 0.13/0.37  # Removed in clause preprocessing      : 4
% 0.13/0.37  # Initial clauses in saturation        : 9
% 0.13/0.37  # Processed clauses                    : 44
% 0.13/0.37  # ...of these trivial                  : 3
% 0.13/0.37  # ...subsumed                          : 6
% 0.13/0.37  # ...remaining for further processing  : 35
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 5
% 0.13/0.37  # Generated clauses                    : 62
% 0.13/0.37  # ...of the previous two non-trivial   : 53
% 0.13/0.37  # Contextual simplify-reflections      : 3
% 0.13/0.37  # Paramodulations                      : 62
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 21
% 0.13/0.37  #    Positive orientable unit clauses  : 8
% 0.13/0.37  #    Positive unorientable unit clauses: 3
% 0.13/0.37  #    Negative unit clauses             : 2
% 0.13/0.37  #    Non-unit-clauses                  : 8
% 0.13/0.37  # Current number of unprocessed clauses: 26
% 0.13/0.37  # ...number of literals in the above   : 39
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 18
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 60
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 57
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 8
% 0.13/0.37  # Unit Clause-clause subsumption calls : 9
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 34
% 0.13/0.37  # BW rewrite match successes           : 23
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1449
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.030 s
% 0.13/0.37  # System time              : 0.003 s
% 0.13/0.37  # Total time               : 0.032 s
% 0.13/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
