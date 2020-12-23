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
% DateTime   : Thu Dec  3 10:44:28 EST 2020

% Result     : Theorem 5.63s
% Output     : CNFRefutation 5.63s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 107 expanded)
%              Number of clauses        :   32 (  50 expanded)
%              Number of leaves         :    7 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :   66 ( 165 expanded)
%              Number of equality atoms :   17 (  58 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t143_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
        & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
     => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(t9_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
          & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
       => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    inference(assume_negation,[status(cth)],[t143_zfmisc_1])).

fof(c_0_8,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,X13)
      | k2_xboole_0(X12,X13) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_9,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))
    & r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))
    & ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X18,X19] : r1_tarski(X18,k2_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_11,plain,(
    ! [X7,X8] : k2_xboole_0(X7,X8) = k2_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_12,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(k2_xboole_0(X9,X10),X11)
      | r1_tarski(X9,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( k2_xboole_0(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)) = k2_zfmisc_1(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_15])).

fof(c_0_23,plain,(
    ! [X23,X24,X25] :
      ( k2_zfmisc_1(k2_xboole_0(X23,X24),X25) = k2_xboole_0(k2_zfmisc_1(X23,X25),k2_zfmisc_1(X24,X25))
      & k2_zfmisc_1(X25,k2_xboole_0(X23,X24)) = k2_xboole_0(k2_zfmisc_1(X25,X23),k2_zfmisc_1(X25,X24)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

cnf(c_0_24,negated_conjecture,
    ( k2_xboole_0(esk1_0,k2_zfmisc_1(esk3_0,esk4_0)) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_19])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_20])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_20])).

fof(c_0_27,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(X20,X21)
      | r1_tarski(k2_xboole_0(X20,X22),k2_xboole_0(X21,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_xboole_1])])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk2_0,k2_xboole_0(k2_xboole_0(k2_zfmisc_1(esk5_0,esk6_0),X1),X2)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk1_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_24])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk2_0,k2_xboole_0(k2_zfmisc_1(esk5_0,k2_xboole_0(esk6_0,X1)),X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(X1,k2_xboole_0(X2,k2_zfmisc_1(esk3_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(k2_xboole_0(X1,X3),X2)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(k2_xboole_0(esk5_0,X1),k2_xboole_0(esk6_0,X2))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(X1,k2_zfmisc_1(esk3_0,k2_xboole_0(X2,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_29])).

cnf(c_0_39,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_16])).

cnf(c_0_40,negated_conjecture,
    ( k2_xboole_0(esk2_0,k2_zfmisc_1(k2_xboole_0(esk5_0,X1),k2_xboole_0(esk6_0,X2))) = k2_zfmisc_1(k2_xboole_0(esk5_0,X1),k2_xboole_0(esk6_0,X2)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(k2_xboole_0(X1,esk3_0),k2_xboole_0(X2,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk2_0,X1),k2_xboole_0(X1,k2_zfmisc_1(k2_xboole_0(esk5_0,X2),k2_xboole_0(esk6_0,X3)))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( k2_xboole_0(esk1_0,k2_zfmisc_1(k2_xboole_0(X1,esk3_0),k2_xboole_0(X2,esk4_0))) = k2_zfmisc_1(k2_xboole_0(X1,esk3_0),k2_xboole_0(X2,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk6_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_42,c_0_16])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_16]),c_0_16]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:11:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 5.63/5.81  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 5.63/5.81  # and selection function SelectNewComplexAHP.
% 5.63/5.81  #
% 5.63/5.81  # Preprocessing time       : 0.026 s
% 5.63/5.81  # Presaturation interreduction done
% 5.63/5.81  
% 5.63/5.81  # Proof found!
% 5.63/5.81  # SZS status Theorem
% 5.63/5.81  # SZS output start CNFRefutation
% 5.63/5.81  fof(t143_zfmisc_1, conjecture, ![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 5.63/5.81  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.63/5.81  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.63/5.81  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.63/5.81  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 5.63/5.81  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 5.63/5.81  fof(t9_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_xboole_1)).
% 5.63/5.81  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))))), inference(assume_negation,[status(cth)],[t143_zfmisc_1])).
% 5.63/5.81  fof(c_0_8, plain, ![X12, X13]:(~r1_tarski(X12,X13)|k2_xboole_0(X12,X13)=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 5.63/5.81  fof(c_0_9, negated_conjecture, ((r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))&r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)))&~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 5.63/5.81  fof(c_0_10, plain, ![X18, X19]:r1_tarski(X18,k2_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 5.63/5.81  fof(c_0_11, plain, ![X7, X8]:k2_xboole_0(X7,X8)=k2_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 5.63/5.81  fof(c_0_12, plain, ![X9, X10, X11]:(~r1_tarski(k2_xboole_0(X9,X10),X11)|r1_tarski(X9,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 5.63/5.81  cnf(c_0_13, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 5.63/5.81  cnf(c_0_14, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 5.63/5.81  cnf(c_0_15, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 5.63/5.81  cnf(c_0_16, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 5.63/5.81  cnf(c_0_17, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 5.63/5.81  cnf(c_0_18, negated_conjecture, (k2_xboole_0(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))=k2_zfmisc_1(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 5.63/5.81  cnf(c_0_19, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 5.63/5.81  cnf(c_0_20, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 5.63/5.81  cnf(c_0_21, negated_conjecture, (r1_tarski(esk2_0,X1)|~r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 5.63/5.81  cnf(c_0_22, plain, (r1_tarski(X1,k2_xboole_0(k2_xboole_0(X1,X2),X3))), inference(spm,[status(thm)],[c_0_17, c_0_15])).
% 5.63/5.81  fof(c_0_23, plain, ![X23, X24, X25]:(k2_zfmisc_1(k2_xboole_0(X23,X24),X25)=k2_xboole_0(k2_zfmisc_1(X23,X25),k2_zfmisc_1(X24,X25))&k2_zfmisc_1(X25,k2_xboole_0(X23,X24))=k2_xboole_0(k2_zfmisc_1(X25,X23),k2_zfmisc_1(X25,X24))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 5.63/5.81  cnf(c_0_24, negated_conjecture, (k2_xboole_0(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))=k2_zfmisc_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_13, c_0_19])).
% 5.63/5.81  cnf(c_0_25, plain, (r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3)))), inference(spm,[status(thm)],[c_0_17, c_0_20])).
% 5.63/5.81  cnf(c_0_26, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_13, c_0_20])).
% 5.63/5.81  fof(c_0_27, plain, ![X20, X21, X22]:(~r1_tarski(X20,X21)|r1_tarski(k2_xboole_0(X20,X22),k2_xboole_0(X21,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_xboole_1])])).
% 5.63/5.81  cnf(c_0_28, negated_conjecture, (r1_tarski(esk2_0,k2_xboole_0(k2_xboole_0(k2_zfmisc_1(esk5_0,esk6_0),X1),X2))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 5.63/5.81  cnf(c_0_29, plain, (k2_zfmisc_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 5.63/5.81  cnf(c_0_30, negated_conjecture, (r1_tarski(esk1_0,X1)|~r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_17, c_0_24])).
% 5.63/5.81  cnf(c_0_31, plain, (r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1)))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 5.63/5.81  cnf(c_0_32, plain, (r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 5.63/5.81  cnf(c_0_33, negated_conjecture, (r1_tarski(esk2_0,k2_xboole_0(k2_zfmisc_1(esk5_0,k2_xboole_0(esk6_0,X1)),X2))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 5.63/5.81  cnf(c_0_34, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 5.63/5.81  cnf(c_0_35, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(X1,k2_xboole_0(X2,k2_zfmisc_1(esk3_0,esk4_0))))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 5.63/5.81  cnf(c_0_36, plain, (r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(k2_xboole_0(X1,X3),X2))), inference(spm,[status(thm)],[c_0_32, c_0_15])).
% 5.63/5.81  cnf(c_0_37, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(k2_xboole_0(esk5_0,X1),k2_xboole_0(esk6_0,X2)))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 5.63/5.81  cnf(c_0_38, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(X1,k2_zfmisc_1(esk3_0,k2_xboole_0(X2,esk4_0))))), inference(spm,[status(thm)],[c_0_35, c_0_29])).
% 5.63/5.81  cnf(c_0_39, plain, (r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X2,k2_xboole_0(X1,X3)))), inference(spm,[status(thm)],[c_0_36, c_0_16])).
% 5.63/5.81  cnf(c_0_40, negated_conjecture, (k2_xboole_0(esk2_0,k2_zfmisc_1(k2_xboole_0(esk5_0,X1),k2_xboole_0(esk6_0,X2)))=k2_zfmisc_1(k2_xboole_0(esk5_0,X1),k2_xboole_0(esk6_0,X2))), inference(spm,[status(thm)],[c_0_13, c_0_37])).
% 5.63/5.81  cnf(c_0_41, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(k2_xboole_0(X1,esk3_0),k2_xboole_0(X2,esk4_0)))), inference(spm,[status(thm)],[c_0_38, c_0_34])).
% 5.63/5.81  cnf(c_0_42, negated_conjecture, (~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 5.63/5.81  cnf(c_0_43, negated_conjecture, (r1_tarski(k2_xboole_0(esk2_0,X1),k2_xboole_0(X1,k2_zfmisc_1(k2_xboole_0(esk5_0,X2),k2_xboole_0(esk6_0,X3))))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 5.63/5.81  cnf(c_0_44, negated_conjecture, (k2_xboole_0(esk1_0,k2_zfmisc_1(k2_xboole_0(X1,esk3_0),k2_xboole_0(X2,esk4_0)))=k2_zfmisc_1(k2_xboole_0(X1,esk3_0),k2_xboole_0(X2,esk4_0))), inference(spm,[status(thm)],[c_0_13, c_0_41])).
% 5.63/5.81  cnf(c_0_45, negated_conjecture, (~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk6_0,esk4_0)))), inference(rw,[status(thm)],[c_0_42, c_0_16])).
% 5.63/5.81  cnf(c_0_46, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_16]), c_0_16]), c_0_45]), ['proof']).
% 5.63/5.81  # SZS output end CNFRefutation
% 5.63/5.81  # Proof object total steps             : 47
% 5.63/5.81  # Proof object clause steps            : 32
% 5.63/5.81  # Proof object formula steps           : 15
% 5.63/5.81  # Proof object conjectures             : 21
% 5.63/5.81  # Proof object clause conjectures      : 18
% 5.63/5.81  # Proof object formula conjectures     : 3
% 5.63/5.81  # Proof object initial clauses used    : 10
% 5.63/5.81  # Proof object initial formulas used   : 7
% 5.63/5.81  # Proof object generating inferences   : 21
% 5.63/5.81  # Proof object simplifying inferences  : 4
% 5.63/5.81  # Training examples: 0 positive, 0 negative
% 5.63/5.81  # Parsed axioms                        : 8
% 5.63/5.81  # Removed by relevancy pruning/SinE    : 0
% 5.63/5.81  # Initial clauses                      : 11
% 5.63/5.81  # Removed in clause preprocessing      : 0
% 5.63/5.81  # Initial clauses in saturation        : 11
% 5.63/5.81  # Processed clauses                    : 19520
% 5.63/5.81  # ...of these trivial                  : 13616
% 5.63/5.81  # ...subsumed                          : 2717
% 5.63/5.81  # ...remaining for further processing  : 3186
% 5.63/5.81  # Other redundant clauses eliminated   : 0
% 5.63/5.81  # Clauses deleted for lack of memory   : 0
% 5.63/5.81  # Backward-subsumed                    : 0
% 5.63/5.81  # Backward-rewritten                   : 865
% 5.63/5.81  # Generated clauses                    : 945742
% 5.63/5.81  # ...of the previous two non-trivial   : 572307
% 5.63/5.81  # Contextual simplify-reflections      : 0
% 5.63/5.81  # Paramodulations                      : 945742
% 5.63/5.81  # Factorizations                       : 0
% 5.63/5.81  # Equation resolutions                 : 0
% 5.63/5.81  # Propositional unsat checks           : 0
% 5.63/5.81  #    Propositional check models        : 0
% 5.63/5.81  #    Propositional check unsatisfiable : 0
% 5.63/5.81  #    Propositional clauses             : 0
% 5.63/5.81  #    Propositional clauses after purity: 0
% 5.63/5.81  #    Propositional unsat core size     : 0
% 5.63/5.81  #    Propositional preprocessing time  : 0.000
% 5.63/5.81  #    Propositional encoding time       : 0.000
% 5.63/5.81  #    Propositional solver time         : 0.000
% 5.63/5.81  #    Success case prop preproc time    : 0.000
% 5.63/5.81  #    Success case prop encoding time   : 0.000
% 5.63/5.81  #    Success case prop solver time     : 0.000
% 5.63/5.81  # Current number of processed clauses  : 2310
% 5.63/5.81  #    Positive orientable unit clauses  : 2030
% 5.63/5.81  #    Positive unorientable unit clauses: 25
% 5.63/5.81  #    Negative unit clauses             : 1
% 5.63/5.81  #    Non-unit-clauses                  : 254
% 5.63/5.81  # Current number of unprocessed clauses: 548424
% 5.63/5.81  # ...number of literals in the above   : 566758
% 5.63/5.81  # Current number of archived formulas  : 0
% 5.63/5.81  # Current number of archived clauses   : 876
% 5.63/5.81  # Clause-clause subsumption calls (NU) : 38257
% 5.63/5.81  # Rec. Clause-clause subsumption calls : 38257
% 5.63/5.81  # Non-unit clause-clause subsumptions  : 2428
% 5.63/5.81  # Unit Clause-clause subsumption calls : 14915
% 5.63/5.81  # Rewrite failures with RHS unbound    : 0
% 5.63/5.81  # BW rewrite match attempts            : 41411
% 5.63/5.81  # BW rewrite match successes           : 2809
% 5.63/5.81  # Condensation attempts                : 0
% 5.63/5.81  # Condensation successes               : 0
% 5.63/5.81  # Termbank termtop insertions          : 15509949
% 5.63/5.84  
% 5.63/5.84  # -------------------------------------------------
% 5.63/5.84  # User time                : 5.208 s
% 5.63/5.84  # System time              : 0.260 s
% 5.63/5.84  # Total time               : 5.468 s
% 5.63/5.84  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
