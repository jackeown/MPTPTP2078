%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:12 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 229 expanded)
%              Number of clauses        :   39 ( 101 expanded)
%              Number of leaves         :   10 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :  125 ( 477 expanded)
%              Number of equality atoms :   72 ( 247 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t127_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_xboole_0(X1,X2)
        | r1_xboole_0(X3,X4) )
     => r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

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

fof(t134_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(c_0_10,plain,(
    ! [X5,X6] :
      ( ( ~ r1_xboole_0(X5,X6)
        | k3_xboole_0(X5,X6) = k1_xboole_0 )
      & ( k3_xboole_0(X5,X6) != k1_xboole_0
        | r1_xboole_0(X5,X6) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_11,plain,(
    ! [X20,X21,X22,X23] :
      ( ( ~ r1_xboole_0(X20,X21)
        | r1_xboole_0(k2_zfmisc_1(X20,X22),k2_zfmisc_1(X21,X23)) )
      & ( ~ r1_xboole_0(X22,X23)
        | r1_xboole_0(k2_zfmisc_1(X20,X22),k2_zfmisc_1(X21,X23)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).

fof(c_0_12,plain,(
    ! [X16,X17,X18,X19] : k2_zfmisc_1(k3_xboole_0(X16,X17),k3_xboole_0(X18,X19)) = k3_xboole_0(k2_zfmisc_1(X16,X18),k2_zfmisc_1(X17,X19)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

cnf(c_0_13,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X7] : k3_xboole_0(X7,X7) = X7 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_17,plain,(
    ! [X14,X15] :
      ( ~ r1_tarski(X14,X15)
      | k3_xboole_0(X14,X15) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
       => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
          | ( r1_tarski(X1,X3)
            & r1_tarski(X2,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t138_zfmisc_1])).

cnf(c_0_19,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k1_xboole_0
    | ~ r1_xboole_0(X3,X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))
    & k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0
    & ( ~ r1_tarski(esk1_0,esk3_0)
      | ~ r1_tarski(esk2_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_23,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),X3) = k1_xboole_0
    | ~ r1_xboole_0(X3,X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k2_zfmisc_1(X1,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),X3) = k1_xboole_0
    | X3 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_20])).

cnf(c_0_28,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_29,plain,(
    ! [X24,X25,X26,X27] :
      ( ( X24 = X26
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0
        | k2_zfmisc_1(X24,X25) != k2_zfmisc_1(X26,X27) )
      & ( X25 = X27
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0
        | k2_zfmisc_1(X24,X25) != k2_zfmisc_1(X26,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_zfmisc_1])])])).

cnf(c_0_30,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk2_0,esk4_0)) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_20])).

fof(c_0_33,plain,(
    ! [X8,X9] :
      ( ( k4_xboole_0(X8,X9) != k1_xboole_0
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | k4_xboole_0(X8,X9) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_34,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_35,plain,(
    ! [X12,X13] : r1_tarski(k3_xboole_0(X12,X13),X12) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_28]),c_0_15])).

cnf(c_0_37,plain,
    ( X1 = X2
    | X1 = k1_xboole_0
    | X3 = k1_xboole_0
    | k2_zfmisc_1(X1,X3) != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),esk2_0) = k2_zfmisc_1(esk1_0,esk2_0)
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_21])).

cnf(c_0_39,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_36]),c_0_31])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk3_0) = k1_xboole_0
    | k3_xboole_0(esk1_0,esk3_0) = X1
    | k2_zfmisc_1(esk1_0,esk2_0) != k2_zfmisc_1(X1,X2)
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_20])).

cnf(c_0_48,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(X3,X1) != k2_zfmisc_1(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_49,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk3_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_24])).

cnf(c_0_50,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk4_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_30]),c_0_31])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_44,c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk3_0) = esk1_0
    | k3_xboole_0(esk1_0,esk3_0) = k1_xboole_0
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_20]),c_0_47])])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk3_0)
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_55,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk4_0) = X1
    | k2_zfmisc_1(esk1_0,esk2_0) != k2_zfmisc_1(X2,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_30]),c_0_49]),c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk3_0) = k1_xboole_0
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])]),c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk4_0) = esk2_0 ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_57]),c_0_53])]),c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:12:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 0.19/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.027 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.19/0.41  fof(t127_zfmisc_1, axiom, ![X1, X2, X3, X4]:((r1_xboole_0(X1,X2)|r1_xboole_0(X3,X4))=>r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 0.19/0.41  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 0.19/0.41  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.19/0.41  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.41  fof(t138_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 0.19/0.41  fof(t134_zfmisc_1, axiom, ![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 0.19/0.41  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.19/0.41  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.41  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.19/0.41  fof(c_0_10, plain, ![X5, X6]:((~r1_xboole_0(X5,X6)|k3_xboole_0(X5,X6)=k1_xboole_0)&(k3_xboole_0(X5,X6)!=k1_xboole_0|r1_xboole_0(X5,X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.19/0.41  fof(c_0_11, plain, ![X20, X21, X22, X23]:((~r1_xboole_0(X20,X21)|r1_xboole_0(k2_zfmisc_1(X20,X22),k2_zfmisc_1(X21,X23)))&(~r1_xboole_0(X22,X23)|r1_xboole_0(k2_zfmisc_1(X20,X22),k2_zfmisc_1(X21,X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).
% 0.19/0.41  fof(c_0_12, plain, ![X16, X17, X18, X19]:k2_zfmisc_1(k3_xboole_0(X16,X17),k3_xboole_0(X18,X19))=k3_xboole_0(k2_zfmisc_1(X16,X18),k2_zfmisc_1(X17,X19)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 0.19/0.41  cnf(c_0_13, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.41  cnf(c_0_14, plain, (r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.41  cnf(c_0_15, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  fof(c_0_16, plain, ![X7]:k3_xboole_0(X7,X7)=X7, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.19/0.41  fof(c_0_17, plain, ![X14, X15]:(~r1_tarski(X14,X15)|k3_xboole_0(X14,X15)=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.41  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4))))), inference(assume_negation,[status(cth)],[t138_zfmisc_1])).
% 0.19/0.41  cnf(c_0_19, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k1_xboole_0|~r1_xboole_0(X3,X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])).
% 0.19/0.41  cnf(c_0_20, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_21, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  fof(c_0_22, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))&(k2_zfmisc_1(esk1_0,esk2_0)!=k1_xboole_0&(~r1_tarski(esk1_0,esk3_0)|~r1_tarski(esk2_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.19/0.41  cnf(c_0_23, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),X3)=k1_xboole_0|~r1_xboole_0(X3,X3)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.41  cnf(c_0_24, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.41  cnf(c_0_25, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k2_zfmisc_1(X1,X3)|~r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(spm,[status(thm)],[c_0_21, c_0_15])).
% 0.19/0.41  cnf(c_0_26, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.41  cnf(c_0_27, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),X3)=k1_xboole_0|X3!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_20])).
% 0.19/0.41  cnf(c_0_28, plain, (r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.41  fof(c_0_29, plain, ![X24, X25, X26, X27]:((X24=X26|(X24=k1_xboole_0|X25=k1_xboole_0)|k2_zfmisc_1(X24,X25)!=k2_zfmisc_1(X26,X27))&(X25=X27|(X24=k1_xboole_0|X25=k1_xboole_0)|k2_zfmisc_1(X24,X25)!=k2_zfmisc_1(X26,X27))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_zfmisc_1])])])).
% 0.19/0.41  cnf(c_0_30, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk2_0,esk4_0))=k2_zfmisc_1(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.41  cnf(c_0_31, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.41  cnf(c_0_32, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_20])).
% 0.19/0.41  fof(c_0_33, plain, ![X8, X9]:((k4_xboole_0(X8,X9)!=k1_xboole_0|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|k4_xboole_0(X8,X9)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.19/0.41  fof(c_0_34, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.41  fof(c_0_35, plain, ![X12, X13]:r1_tarski(k3_xboole_0(X12,X13),X12), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.19/0.41  cnf(c_0_36, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_28]), c_0_15])).
% 0.19/0.41  cnf(c_0_37, plain, (X1=X2|X1=k1_xboole_0|X3=k1_xboole_0|k2_zfmisc_1(X1,X3)!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.41  cnf(c_0_38, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),esk2_0)=k2_zfmisc_1(esk1_0,esk2_0)|~r1_tarski(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_30, c_0_21])).
% 0.19/0.41  cnf(c_0_39, negated_conjecture, (esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.41  cnf(c_0_40, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.41  cnf(c_0_41, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.41  cnf(c_0_42, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.41  cnf(c_0_43, negated_conjecture, (~r1_xboole_0(esk1_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_36]), c_0_31])).
% 0.19/0.41  cnf(c_0_44, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.41  cnf(c_0_45, negated_conjecture, (k3_xboole_0(esk1_0,esk3_0)=k1_xboole_0|k3_xboole_0(esk1_0,esk3_0)=X1|k2_zfmisc_1(esk1_0,esk2_0)!=k2_zfmisc_1(X1,X2)|~r1_tarski(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.19/0.41  cnf(c_0_46, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.41  cnf(c_0_47, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_42, c_0_20])).
% 0.19/0.41  cnf(c_0_48, plain, (X1=X2|X3=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(X3,X1)!=k2_zfmisc_1(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.41  cnf(c_0_49, negated_conjecture, (k3_xboole_0(esk1_0,esk3_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_24])).
% 0.19/0.41  cnf(c_0_50, negated_conjecture, (k3_xboole_0(esk2_0,esk4_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_30]), c_0_31])).
% 0.19/0.41  cnf(c_0_51, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_44, c_0_41])).
% 0.19/0.41  cnf(c_0_52, negated_conjecture, (k3_xboole_0(esk1_0,esk3_0)=esk1_0|k3_xboole_0(esk1_0,esk3_0)=k1_xboole_0|~r1_tarski(esk2_0,esk4_0)), inference(er,[status(thm)],[c_0_45])).
% 0.19/0.41  cnf(c_0_53, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_20]), c_0_47])])).
% 0.19/0.41  cnf(c_0_54, negated_conjecture, (~r1_tarski(esk1_0,esk3_0)|~r1_tarski(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.41  cnf(c_0_55, negated_conjecture, (k3_xboole_0(esk2_0,esk4_0)=X1|k2_zfmisc_1(esk1_0,esk2_0)!=k2_zfmisc_1(X2,X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_30]), c_0_49]), c_0_50])).
% 0.19/0.41  cnf(c_0_56, negated_conjecture, (k3_xboole_0(esk1_0,esk3_0)=k1_xboole_0|~r1_tarski(esk2_0,esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])]), c_0_54])).
% 0.19/0.41  cnf(c_0_57, negated_conjecture, (k3_xboole_0(esk2_0,esk4_0)=esk2_0), inference(er,[status(thm)],[c_0_55])).
% 0.19/0.41  cnf(c_0_58, negated_conjecture, (~r1_tarski(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_49, c_0_56])).
% 0.19/0.41  cnf(c_0_59, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_57]), c_0_53])]), c_0_58]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 60
% 0.19/0.41  # Proof object clause steps            : 39
% 0.19/0.41  # Proof object formula steps           : 21
% 0.19/0.41  # Proof object conjectures             : 19
% 0.19/0.41  # Proof object clause conjectures      : 16
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 16
% 0.19/0.41  # Proof object initial formulas used   : 10
% 0.19/0.41  # Proof object generating inferences   : 21
% 0.19/0.41  # Proof object simplifying inferences  : 18
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 10
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 16
% 0.19/0.41  # Removed in clause preprocessing      : 1
% 0.19/0.41  # Initial clauses in saturation        : 15
% 0.19/0.41  # Processed clauses                    : 480
% 0.19/0.41  # ...of these trivial                  : 20
% 0.19/0.41  # ...subsumed                          : 242
% 0.19/0.41  # ...remaining for further processing  : 218
% 0.19/0.41  # Other redundant clauses eliminated   : 8
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 33
% 0.19/0.41  # Backward-rewritten                   : 36
% 0.19/0.41  # Generated clauses                    : 3014
% 0.19/0.41  # ...of the previous two non-trivial   : 2274
% 0.19/0.41  # Contextual simplify-reflections      : 4
% 0.19/0.41  # Paramodulations                      : 2991
% 0.19/0.41  # Factorizations                       : 4
% 0.19/0.41  # Equation resolutions                 : 19
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 134
% 0.19/0.41  #    Positive orientable unit clauses  : 19
% 0.19/0.41  #    Positive unorientable unit clauses: 0
% 0.19/0.41  #    Negative unit clauses             : 10
% 0.19/0.41  #    Non-unit-clauses                  : 105
% 0.19/0.41  # Current number of unprocessed clauses: 1693
% 0.19/0.41  # ...number of literals in the above   : 4294
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 85
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 1685
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 1660
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 76
% 0.19/0.41  # Unit Clause-clause subsumption calls : 37
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 25
% 0.19/0.41  # BW rewrite match successes           : 10
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 31931
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.063 s
% 0.19/0.41  # System time              : 0.007 s
% 0.19/0.41  # Total time               : 0.070 s
% 0.19/0.41  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
