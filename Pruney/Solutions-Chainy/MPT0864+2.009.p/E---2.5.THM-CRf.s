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
% DateTime   : Thu Dec  3 10:59:19 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 518 expanded)
%              Number of clauses        :   29 ( 211 expanded)
%              Number of leaves         :   11 ( 145 expanded)
%              Depth                    :    8
%              Number of atoms          :   79 ( 723 expanded)
%              Number of equality atoms :   62 ( 652 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t20_mcart_1,conjecture,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(t35_zfmisc_1,axiom,(
    ! [X1,X2] : k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(t135_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X1,X2))
        | r1_tarski(X1,k2_zfmisc_1(X2,X1)) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_11,plain,(
    ! [X13,X14] : k3_tarski(k2_tarski(X13,X14)) = k2_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X8,X9] : k1_enumset1(X8,X8,X9) = k2_tarski(X8,X9) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
       => ( X1 != k1_mcart_1(X1)
          & X1 != k2_mcart_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t20_mcart_1])).

fof(c_0_14,plain,(
    ! [X17,X18] : k2_zfmisc_1(k1_tarski(X17),k1_tarski(X18)) = k1_tarski(k4_tarski(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t35_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X7] : k2_tarski(X7,X7) = k1_tarski(X7) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_16,plain,(
    ! [X10,X11,X12] : k2_enumset1(X10,X10,X11,X12) = k1_enumset1(X10,X11,X12) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,plain,(
    ! [X19,X20] : k2_xboole_0(k1_tarski(X19),X20) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

cnf(c_0_18,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,plain,(
    ! [X4] : k2_xboole_0(X4,X4) = X4 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_21,plain,(
    ! [X21,X22] :
      ( k1_mcart_1(k4_tarski(X21,X22)) = X21
      & k2_mcart_1(k4_tarski(X21,X22)) = X22 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

fof(c_0_22,negated_conjecture,
    ( esk1_0 = k4_tarski(esk2_0,esk3_0)
    & ( esk1_0 = k1_mcart_1(esk1_0)
      | esk1_0 = k2_mcart_1(esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_23,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( esk1_0 = k4_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,plain,(
    ! [X15,X16] :
      ( ( ~ r1_tarski(X15,k2_zfmisc_1(X15,X16))
        | X15 = k1_xboole_0 )
      & ( ~ r1_tarski(X15,k2_zfmisc_1(X16,X15))
        | X15 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).

cnf(c_0_32,plain,
    ( k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_24]),c_0_24]),c_0_19]),c_0_19]),c_0_19]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_33,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_24]),c_0_19]),c_0_27]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_34,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_27]),c_0_25])).

cnf(c_0_35,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,negated_conjecture,
    ( esk1_0 = k1_mcart_1(esk1_0)
    | esk1_0 = k2_mcart_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_37,negated_conjecture,
    ( k1_mcart_1(esk1_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_38,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_39,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( k2_zfmisc_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) = k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_30])).

cnf(c_0_41,plain,
    ( k2_enumset1(X1,X1,X1,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( k2_mcart_1(esk1_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_30])).

cnf(c_0_43,negated_conjecture,
    ( k2_mcart_1(esk1_0) = esk1_0
    | esk2_0 = esk1_0 ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tarski(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( esk2_0 = esk1_0
    | esk3_0 = esk1_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( ~ r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_40]),c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( esk2_0 = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_48])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n009.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 13:03:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.34  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.34  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.34  #
% 0.12/0.34  # Preprocessing time       : 0.014 s
% 0.12/0.34  # Presaturation interreduction done
% 0.12/0.34  
% 0.12/0.34  # Proof found!
% 0.12/0.34  # SZS status Theorem
% 0.12/0.34  # SZS output start CNFRefutation
% 0.12/0.34  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.12/0.34  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.34  fof(t20_mcart_1, conjecture, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.12/0.34  fof(t35_zfmisc_1, axiom, ![X1, X2]:k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 0.12/0.34  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.34  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.34  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.12/0.34  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.12/0.34  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.12/0.34  fof(t135_zfmisc_1, axiom, ![X1, X2]:((r1_tarski(X1,k2_zfmisc_1(X1,X2))|r1_tarski(X1,k2_zfmisc_1(X2,X1)))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 0.12/0.34  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.34  fof(c_0_11, plain, ![X13, X14]:k3_tarski(k2_tarski(X13,X14))=k2_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.12/0.34  fof(c_0_12, plain, ![X8, X9]:k1_enumset1(X8,X8,X9)=k2_tarski(X8,X9), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.34  fof(c_0_13, negated_conjecture, ~(![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1)))), inference(assume_negation,[status(cth)],[t20_mcart_1])).
% 0.12/0.34  fof(c_0_14, plain, ![X17, X18]:k2_zfmisc_1(k1_tarski(X17),k1_tarski(X18))=k1_tarski(k4_tarski(X17,X18)), inference(variable_rename,[status(thm)],[t35_zfmisc_1])).
% 0.12/0.34  fof(c_0_15, plain, ![X7]:k2_tarski(X7,X7)=k1_tarski(X7), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.34  fof(c_0_16, plain, ![X10, X11, X12]:k2_enumset1(X10,X10,X11,X12)=k1_enumset1(X10,X11,X12), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.34  fof(c_0_17, plain, ![X19, X20]:k2_xboole_0(k1_tarski(X19),X20)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.12/0.34  cnf(c_0_18, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.34  cnf(c_0_19, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.34  fof(c_0_20, plain, ![X4]:k2_xboole_0(X4,X4)=X4, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.12/0.34  fof(c_0_21, plain, ![X21, X22]:(k1_mcart_1(k4_tarski(X21,X22))=X21&k2_mcart_1(k4_tarski(X21,X22))=X22), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.12/0.34  fof(c_0_22, negated_conjecture, (esk1_0=k4_tarski(esk2_0,esk3_0)&(esk1_0=k1_mcart_1(esk1_0)|esk1_0=k2_mcart_1(esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.12/0.34  cnf(c_0_23, plain, (k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.34  cnf(c_0_24, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.34  cnf(c_0_25, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.34  cnf(c_0_26, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.34  cnf(c_0_27, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.34  cnf(c_0_28, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.34  cnf(c_0_29, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.34  cnf(c_0_30, negated_conjecture, (esk1_0=k4_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.34  fof(c_0_31, plain, ![X15, X16]:((~r1_tarski(X15,k2_zfmisc_1(X15,X16))|X15=k1_xboole_0)&(~r1_tarski(X15,k2_zfmisc_1(X16,X15))|X15=k1_xboole_0)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).
% 0.12/0.34  cnf(c_0_32, plain, (k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))=k2_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_24]), c_0_24]), c_0_19]), c_0_19]), c_0_19]), c_0_25]), c_0_25]), c_0_25])).
% 0.12/0.34  cnf(c_0_33, plain, (k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),X2))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_24]), c_0_19]), c_0_27]), c_0_25]), c_0_25]), c_0_25])).
% 0.12/0.34  cnf(c_0_34, plain, (k3_tarski(k2_enumset1(X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_27]), c_0_25])).
% 0.12/0.34  cnf(c_0_35, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.34  cnf(c_0_36, negated_conjecture, (esk1_0=k1_mcart_1(esk1_0)|esk1_0=k2_mcart_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.34  cnf(c_0_37, negated_conjecture, (k1_mcart_1(esk1_0)=esk2_0), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.12/0.34  fof(c_0_38, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.34  cnf(c_0_39, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.34  cnf(c_0_40, negated_conjecture, (k2_zfmisc_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))=k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)), inference(spm,[status(thm)],[c_0_32, c_0_30])).
% 0.12/0.34  cnf(c_0_41, plain, (k2_enumset1(X1,X1,X1,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.12/0.34  cnf(c_0_42, negated_conjecture, (k2_mcart_1(esk1_0)=esk3_0), inference(spm,[status(thm)],[c_0_35, c_0_30])).
% 0.12/0.34  cnf(c_0_43, negated_conjecture, (k2_mcart_1(esk1_0)=esk1_0|esk2_0=esk1_0), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.12/0.34  cnf(c_0_44, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.12/0.34  cnf(c_0_45, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.34  cnf(c_0_46, negated_conjecture, (~r1_tarski(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.12/0.34  cnf(c_0_47, negated_conjecture, (esk2_0=esk1_0|esk3_0=esk1_0), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.12/0.34  cnf(c_0_48, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_44])).
% 0.12/0.34  cnf(c_0_49, negated_conjecture, (~r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_40]), c_0_41])).
% 0.12/0.34  cnf(c_0_50, negated_conjecture, (esk2_0=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])])).
% 0.12/0.34  cnf(c_0_51, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_48])]), ['proof']).
% 0.12/0.34  # SZS output end CNFRefutation
% 0.12/0.34  # Proof object total steps             : 52
% 0.12/0.34  # Proof object clause steps            : 29
% 0.12/0.34  # Proof object formula steps           : 23
% 0.12/0.34  # Proof object conjectures             : 14
% 0.12/0.34  # Proof object clause conjectures      : 11
% 0.12/0.34  # Proof object formula conjectures     : 3
% 0.12/0.34  # Proof object initial clauses used    : 14
% 0.12/0.34  # Proof object initial formulas used   : 11
% 0.12/0.34  # Proof object generating inferences   : 8
% 0.12/0.34  # Proof object simplifying inferences  : 30
% 0.12/0.34  # Training examples: 0 positive, 0 negative
% 0.12/0.34  # Parsed axioms                        : 11
% 0.12/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.34  # Initial clauses                      : 16
% 0.12/0.34  # Removed in clause preprocessing      : 4
% 0.12/0.34  # Initial clauses in saturation        : 12
% 0.12/0.34  # Processed clauses                    : 40
% 0.12/0.34  # ...of these trivial                  : 0
% 0.12/0.34  # ...subsumed                          : 2
% 0.12/0.34  # ...remaining for further processing  : 38
% 0.12/0.34  # Other redundant clauses eliminated   : 2
% 0.12/0.34  # Clauses deleted for lack of memory   : 0
% 0.12/0.34  # Backward-subsumed                    : 0
% 0.12/0.34  # Backward-rewritten                   : 8
% 0.12/0.34  # Generated clauses                    : 46
% 0.12/0.34  # ...of the previous two non-trivial   : 44
% 0.12/0.34  # Contextual simplify-reflections      : 0
% 0.12/0.34  # Paramodulations                      : 44
% 0.12/0.34  # Factorizations                       : 0
% 0.12/0.34  # Equation resolutions                 : 2
% 0.12/0.34  # Propositional unsat checks           : 0
% 0.12/0.34  #    Propositional check models        : 0
% 0.12/0.34  #    Propositional check unsatisfiable : 0
% 0.12/0.34  #    Propositional clauses             : 0
% 0.12/0.34  #    Propositional clauses after purity: 0
% 0.12/0.34  #    Propositional unsat core size     : 0
% 0.12/0.34  #    Propositional preprocessing time  : 0.000
% 0.12/0.34  #    Propositional encoding time       : 0.000
% 0.12/0.34  #    Propositional solver time         : 0.000
% 0.12/0.34  #    Success case prop preproc time    : 0.000
% 0.12/0.34  #    Success case prop encoding time   : 0.000
% 0.12/0.34  #    Success case prop solver time     : 0.000
% 0.12/0.34  # Current number of processed clauses  : 17
% 0.12/0.34  #    Positive orientable unit clauses  : 8
% 0.12/0.34  #    Positive unorientable unit clauses: 0
% 0.12/0.34  #    Negative unit clauses             : 6
% 0.12/0.34  #    Non-unit-clauses                  : 3
% 0.12/0.34  # Current number of unprocessed clauses: 27
% 0.12/0.34  # ...number of literals in the above   : 35
% 0.12/0.34  # Current number of archived formulas  : 0
% 0.12/0.34  # Current number of archived clauses   : 23
% 0.12/0.34  # Clause-clause subsumption calls (NU) : 5
% 0.12/0.34  # Rec. Clause-clause subsumption calls : 5
% 0.12/0.34  # Non-unit clause-clause subsumptions  : 1
% 0.12/0.34  # Unit Clause-clause subsumption calls : 3
% 0.12/0.34  # Rewrite failures with RHS unbound    : 0
% 0.12/0.34  # BW rewrite match attempts            : 2
% 0.12/0.34  # BW rewrite match successes           : 2
% 0.12/0.34  # Condensation attempts                : 0
% 0.12/0.34  # Condensation successes               : 0
% 0.12/0.34  # Termbank termtop insertions          : 1194
% 0.12/0.34  
% 0.12/0.34  # -------------------------------------------------
% 0.12/0.34  # User time                : 0.014 s
% 0.12/0.34  # System time              : 0.004 s
% 0.12/0.34  # Total time               : 0.018 s
% 0.12/0.34  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
