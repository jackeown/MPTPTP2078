%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:12 EST 2020

% Result     : Theorem 0.38s
% Output     : CNFRefutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 144 expanded)
%              Number of clauses        :   37 (  63 expanded)
%              Number of leaves         :   11 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   97 ( 262 expanded)
%              Number of equality atoms :   65 ( 177 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t138_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
     => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
        | ( r1_tarski(X1,X3)
          & r1_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t125_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k4_xboole_0(X1,X2)) = k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(c_0_11,plain,(
    ! [X13,X14] : r1_tarski(k3_xboole_0(X13,X14),X13) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_12,plain,(
    ! [X20,X21,X22,X23] : k2_zfmisc_1(k3_xboole_0(X20,X21),k3_xboole_0(X22,X23)) = k3_xboole_0(k2_zfmisc_1(X20,X22),k2_zfmisc_1(X21,X23)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k3_xboole_0(X15,X16) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
       => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
          | ( r1_tarski(X1,X3)
            & r1_tarski(X2,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t138_zfmisc_1])).

cnf(c_0_15,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X5] : k3_xboole_0(X5,X5) = X5 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))
    & k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0
    & ( ~ r1_tarski(esk1_0,esk3_0)
      | ~ r1_tarski(esk2_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_20,plain,(
    ! [X24,X25,X26] :
      ( k2_zfmisc_1(k4_xboole_0(X24,X25),X26) = k4_xboole_0(k2_zfmisc_1(X24,X26),k2_zfmisc_1(X25,X26))
      & k2_zfmisc_1(X26,k4_xboole_0(X24,X25)) = k4_xboole_0(k2_zfmisc_1(X26,X24),k2_zfmisc_1(X26,X25)) ) ),
    inference(variable_rename,[status(thm)],[t125_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_22,plain,
    ( r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)),k2_zfmisc_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k2_zfmisc_1(X1,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X10,X11,X12] : k3_xboole_0(k3_xboole_0(X10,X11),X12) = k3_xboole_0(X10,k3_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_27,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk2_0,esk4_0)) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) = k5_xboole_0(k2_zfmisc_1(X1,X3),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_28])).

fof(c_0_34,plain,(
    ! [X17] : k5_xboole_0(X17,X17) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_35,plain,(
    ! [X18,X19] :
      ( ( k2_zfmisc_1(X18,X19) != k1_xboole_0
        | X18 = k1_xboole_0
        | X19 = k1_xboole_0 )
      & ( X18 != k1_xboole_0
        | k2_zfmisc_1(X18,X19) = k1_xboole_0 )
      & ( X19 != k1_xboole_0
        | k2_zfmisc_1(X18,X19) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_28]),c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_23])).

fof(c_0_39,plain,(
    ! [X6,X7] :
      ( ( k4_xboole_0(X6,X7) != k1_xboole_0
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | k4_xboole_0(X6,X7) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_40,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X1,X3),X2)) = k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_16]),c_0_23])).

cnf(c_0_41,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),esk2_0) = k2_zfmisc_1(esk1_0,esk2_0)
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_18])).

cnf(c_0_42,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_44,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_xboole_0(X2,X3))) = k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_16]),c_0_23])).

cnf(c_0_46,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0)) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_37]),c_0_23]),c_0_38])).

cnf(c_0_47,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_50,negated_conjecture,
    ( k2_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)),esk2_0) = k1_xboole_0
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_47])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_48,c_0_28])).

cnf(c_0_55,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)) = k1_xboole_0
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk3_0)
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_57,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_52]),c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_57]),c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:36:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.38/0.61  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 0.38/0.61  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.38/0.61  #
% 0.38/0.61  # Preprocessing time       : 0.026 s
% 0.38/0.61  # Presaturation interreduction done
% 0.38/0.61  
% 0.38/0.61  # Proof found!
% 0.38/0.61  # SZS status Theorem
% 0.38/0.61  # SZS output start CNFRefutation
% 0.38/0.61  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.38/0.61  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 0.38/0.61  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.38/0.61  fof(t138_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 0.38/0.61  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.38/0.61  fof(t125_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k4_xboole_0(X1,X2))=k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 0.38/0.61  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.38/0.61  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.38/0.61  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.38/0.61  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.38/0.61  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.38/0.61  fof(c_0_11, plain, ![X13, X14]:r1_tarski(k3_xboole_0(X13,X14),X13), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.38/0.61  fof(c_0_12, plain, ![X20, X21, X22, X23]:k2_zfmisc_1(k3_xboole_0(X20,X21),k3_xboole_0(X22,X23))=k3_xboole_0(k2_zfmisc_1(X20,X22),k2_zfmisc_1(X21,X23)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 0.38/0.61  fof(c_0_13, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k3_xboole_0(X15,X16)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.38/0.61  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4))))), inference(assume_negation,[status(cth)],[t138_zfmisc_1])).
% 0.38/0.61  cnf(c_0_15, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.38/0.61  cnf(c_0_16, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.38/0.61  fof(c_0_17, plain, ![X5]:k3_xboole_0(X5,X5)=X5, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.38/0.61  cnf(c_0_18, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.38/0.61  fof(c_0_19, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))&(k2_zfmisc_1(esk1_0,esk2_0)!=k1_xboole_0&(~r1_tarski(esk1_0,esk3_0)|~r1_tarski(esk2_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.38/0.61  fof(c_0_20, plain, ![X24, X25, X26]:(k2_zfmisc_1(k4_xboole_0(X24,X25),X26)=k4_xboole_0(k2_zfmisc_1(X24,X26),k2_zfmisc_1(X25,X26))&k2_zfmisc_1(X26,k4_xboole_0(X24,X25))=k4_xboole_0(k2_zfmisc_1(X26,X24),k2_zfmisc_1(X26,X25))), inference(variable_rename,[status(thm)],[t125_zfmisc_1])).
% 0.38/0.61  fof(c_0_21, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.38/0.61  cnf(c_0_22, plain, (r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)),k2_zfmisc_1(X1,X3))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.38/0.61  cnf(c_0_23, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.38/0.61  cnf(c_0_24, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k2_zfmisc_1(X1,X3)|~r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(spm,[status(thm)],[c_0_18, c_0_16])).
% 0.38/0.61  cnf(c_0_25, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.38/0.61  fof(c_0_26, plain, ![X10, X11, X12]:k3_xboole_0(k3_xboole_0(X10,X11),X12)=k3_xboole_0(X10,k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.38/0.61  cnf(c_0_27, plain, (k2_zfmisc_1(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.38/0.61  cnf(c_0_28, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.38/0.61  cnf(c_0_29, plain, (k2_zfmisc_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.38/0.61  cnf(c_0_30, plain, (r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(X1,X3))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.38/0.61  cnf(c_0_31, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk2_0,esk4_0))=k2_zfmisc_1(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.38/0.61  cnf(c_0_32, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.38/0.61  cnf(c_0_33, plain, (k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)=k5_xboole_0(k2_zfmisc_1(X1,X3),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_28])).
% 0.38/0.61  fof(c_0_34, plain, ![X17]:k5_xboole_0(X17,X17)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.38/0.61  fof(c_0_35, plain, ![X18, X19]:((k2_zfmisc_1(X18,X19)!=k1_xboole_0|(X18=k1_xboole_0|X19=k1_xboole_0))&((X18!=k1_xboole_0|k2_zfmisc_1(X18,X19)=k1_xboole_0)&(X19!=k1_xboole_0|k2_zfmisc_1(X18,X19)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.38/0.61  cnf(c_0_36, plain, (k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_28]), c_0_28])).
% 0.38/0.61  cnf(c_0_37, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.38/0.61  cnf(c_0_38, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_32, c_0_23])).
% 0.38/0.61  fof(c_0_39, plain, ![X6, X7]:((k4_xboole_0(X6,X7)!=k1_xboole_0|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|k4_xboole_0(X6,X7)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.38/0.61  cnf(c_0_40, plain, (k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X1,X3),X2))=k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_16]), c_0_23])).
% 0.38/0.61  cnf(c_0_41, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),esk2_0)=k2_zfmisc_1(esk1_0,esk2_0)|~r1_tarski(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_31, c_0_18])).
% 0.38/0.61  cnf(c_0_42, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.38/0.61  cnf(c_0_43, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.38/0.61  cnf(c_0_44, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.38/0.61  cnf(c_0_45, plain, (k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_xboole_0(X2,X3)))=k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_16]), c_0_23])).
% 0.38/0.61  cnf(c_0_46, negated_conjecture, (k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0))=k2_zfmisc_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_37]), c_0_23]), c_0_38])).
% 0.38/0.61  cnf(c_0_47, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.38/0.61  cnf(c_0_48, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.38/0.61  cnf(c_0_49, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.38/0.61  cnf(c_0_50, negated_conjecture, (k2_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)),esk2_0)=k1_xboole_0|~r1_tarski(esk2_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.38/0.61  cnf(c_0_51, negated_conjecture, (esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.38/0.61  cnf(c_0_52, negated_conjecture, (k2_zfmisc_1(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_42])).
% 0.38/0.61  cnf(c_0_53, negated_conjecture, (esk1_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_47])).
% 0.38/0.61  cnf(c_0_54, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_48, c_0_28])).
% 0.38/0.61  cnf(c_0_55, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0))=k1_xboole_0|~r1_tarski(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.38/0.61  cnf(c_0_56, negated_conjecture, (~r1_tarski(esk1_0,esk3_0)|~r1_tarski(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.38/0.61  cnf(c_0_57, negated_conjecture, (k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0))=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_52]), c_0_53])).
% 0.38/0.61  cnf(c_0_58, negated_conjecture, (~r1_tarski(esk2_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 0.38/0.61  cnf(c_0_59, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_57]), c_0_58]), ['proof']).
% 0.38/0.61  # SZS output end CNFRefutation
% 0.38/0.61  # Proof object total steps             : 60
% 0.38/0.61  # Proof object clause steps            : 37
% 0.38/0.61  # Proof object formula steps           : 23
% 0.38/0.61  # Proof object conjectures             : 18
% 0.38/0.61  # Proof object clause conjectures      : 15
% 0.38/0.61  # Proof object formula conjectures     : 3
% 0.38/0.61  # Proof object initial clauses used    : 16
% 0.38/0.61  # Proof object initial formulas used   : 11
% 0.38/0.61  # Proof object generating inferences   : 16
% 0.38/0.61  # Proof object simplifying inferences  : 17
% 0.38/0.61  # Training examples: 0 positive, 0 negative
% 0.38/0.61  # Parsed axioms                        : 11
% 0.38/0.61  # Removed by relevancy pruning/SinE    : 0
% 0.38/0.61  # Initial clauses                      : 17
% 0.38/0.61  # Removed in clause preprocessing      : 1
% 0.38/0.61  # Initial clauses in saturation        : 16
% 0.38/0.61  # Processed clauses                    : 2894
% 0.38/0.61  # ...of these trivial                  : 23
% 0.38/0.61  # ...subsumed                          : 2427
% 0.38/0.61  # ...remaining for further processing  : 444
% 0.38/0.61  # Other redundant clauses eliminated   : 0
% 0.38/0.61  # Clauses deleted for lack of memory   : 0
% 0.38/0.61  # Backward-subsumed                    : 48
% 0.38/0.61  # Backward-rewritten                   : 14
% 0.38/0.61  # Generated clauses                    : 22551
% 0.38/0.61  # ...of the previous two non-trivial   : 19276
% 0.38/0.61  # Contextual simplify-reflections      : 9
% 0.38/0.61  # Paramodulations                      : 22550
% 0.38/0.61  # Factorizations                       : 0
% 0.38/0.61  # Equation resolutions                 : 1
% 0.38/0.61  # Propositional unsat checks           : 0
% 0.38/0.61  #    Propositional check models        : 0
% 0.38/0.61  #    Propositional check unsatisfiable : 0
% 0.38/0.61  #    Propositional clauses             : 0
% 0.38/0.61  #    Propositional clauses after purity: 0
% 0.38/0.61  #    Propositional unsat core size     : 0
% 0.38/0.61  #    Propositional preprocessing time  : 0.000
% 0.38/0.61  #    Propositional encoding time       : 0.000
% 0.38/0.61  #    Propositional solver time         : 0.000
% 0.38/0.61  #    Success case prop preproc time    : 0.000
% 0.38/0.61  #    Success case prop encoding time   : 0.000
% 0.38/0.61  #    Success case prop solver time     : 0.000
% 0.38/0.61  # Current number of processed clauses  : 366
% 0.38/0.61  #    Positive orientable unit clauses  : 48
% 0.38/0.61  #    Positive unorientable unit clauses: 0
% 0.38/0.61  #    Negative unit clauses             : 7
% 0.38/0.61  #    Non-unit-clauses                  : 311
% 0.38/0.61  # Current number of unprocessed clauses: 16265
% 0.38/0.61  # ...number of literals in the above   : 46228
% 0.38/0.61  # Current number of archived formulas  : 0
% 0.38/0.61  # Current number of archived clauses   : 79
% 0.38/0.61  # Clause-clause subsumption calls (NU) : 37587
% 0.38/0.61  # Rec. Clause-clause subsumption calls : 26541
% 0.38/0.61  # Non-unit clause-clause subsumptions  : 2058
% 0.38/0.61  # Unit Clause-clause subsumption calls : 109
% 0.38/0.61  # Rewrite failures with RHS unbound    : 0
% 0.38/0.61  # BW rewrite match attempts            : 89
% 0.38/0.61  # BW rewrite match successes           : 9
% 0.38/0.61  # Condensation attempts                : 0
% 0.38/0.61  # Condensation successes               : 0
% 0.38/0.61  # Termbank termtop insertions          : 272970
% 0.38/0.61  
% 0.38/0.61  # -------------------------------------------------
% 0.38/0.61  # User time                : 0.251 s
% 0.38/0.61  # System time              : 0.018 s
% 0.38/0.61  # Total time               : 0.269 s
% 0.38/0.61  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
