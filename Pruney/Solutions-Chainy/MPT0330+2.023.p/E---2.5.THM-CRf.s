%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:28 EST 2020

% Result     : Theorem 0.95s
% Output     : CNFRefutation 0.95s
% Verified   : 
% Statistics : Number of formulae       :   43 (  88 expanded)
%              Number of clauses        :   28 (  41 expanded)
%              Number of leaves         :    7 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :   66 ( 144 expanded)
%              Number of equality atoms :   15 (  44 expanded)
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

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

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
    ! [X14,X15] : r1_tarski(X14,k2_xboole_0(X14,X15)) ),
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
    ! [X19,X20,X21] :
      ( k2_zfmisc_1(k2_xboole_0(X19,X20),X21) = k2_xboole_0(k2_zfmisc_1(X19,X21),k2_zfmisc_1(X20,X21))
      & k2_zfmisc_1(X21,k2_xboole_0(X19,X20)) = k2_xboole_0(k2_zfmisc_1(X21,X19),k2_zfmisc_1(X21,X20)) ) ),
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

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk2_0,k2_xboole_0(k2_xboole_0(k2_zfmisc_1(esk5_0,esk6_0),X1),X2)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk1_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_24])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_31,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_tarski(X16,X17)
      | ~ r1_tarski(X18,X17)
      | r1_tarski(k2_xboole_0(X16,X18),X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk2_0,k2_xboole_0(k2_zfmisc_1(esk5_0,k2_xboole_0(esk6_0,X1)),X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(X1,k2_xboole_0(X2,k2_zfmisc_1(esk3_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(k2_xboole_0(esk5_0,X1),k2_xboole_0(esk6_0,X2))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(X1,k2_zfmisc_1(esk3_0,k2_xboole_0(X2,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,esk2_0),k2_zfmisc_1(k2_xboole_0(esk5_0,X2),k2_xboole_0(esk6_0,X3)))
    | ~ r1_tarski(X1,k2_zfmisc_1(k2_xboole_0(esk5_0,X2),k2_xboole_0(esk6_0,X3))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(k2_xboole_0(X1,esk3_0),k2_xboole_0(X2,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk6_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_38,c_0_16])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_16]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:50:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.95/1.14  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.95/1.14  # and selection function SelectNewComplexAHP.
% 0.95/1.14  #
% 0.95/1.14  # Preprocessing time       : 0.026 s
% 0.95/1.14  # Presaturation interreduction done
% 0.95/1.14  
% 0.95/1.14  # Proof found!
% 0.95/1.14  # SZS status Theorem
% 0.95/1.14  # SZS output start CNFRefutation
% 0.95/1.14  fof(t143_zfmisc_1, conjecture, ![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 0.95/1.14  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.95/1.14  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.95/1.14  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.95/1.14  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.95/1.14  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 0.95/1.14  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.95/1.14  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))))), inference(assume_negation,[status(cth)],[t143_zfmisc_1])).
% 0.95/1.14  fof(c_0_8, plain, ![X12, X13]:(~r1_tarski(X12,X13)|k2_xboole_0(X12,X13)=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.95/1.14  fof(c_0_9, negated_conjecture, ((r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))&r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)))&~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.95/1.14  fof(c_0_10, plain, ![X14, X15]:r1_tarski(X14,k2_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.95/1.14  fof(c_0_11, plain, ![X7, X8]:k2_xboole_0(X7,X8)=k2_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.95/1.14  fof(c_0_12, plain, ![X9, X10, X11]:(~r1_tarski(k2_xboole_0(X9,X10),X11)|r1_tarski(X9,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.95/1.14  cnf(c_0_13, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.95/1.14  cnf(c_0_14, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.95/1.14  cnf(c_0_15, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.95/1.14  cnf(c_0_16, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.95/1.14  cnf(c_0_17, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.95/1.14  cnf(c_0_18, negated_conjecture, (k2_xboole_0(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))=k2_zfmisc_1(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.95/1.14  cnf(c_0_19, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.95/1.14  cnf(c_0_20, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.95/1.14  cnf(c_0_21, negated_conjecture, (r1_tarski(esk2_0,X1)|~r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.95/1.14  cnf(c_0_22, plain, (r1_tarski(X1,k2_xboole_0(k2_xboole_0(X1,X2),X3))), inference(spm,[status(thm)],[c_0_17, c_0_15])).
% 0.95/1.14  fof(c_0_23, plain, ![X19, X20, X21]:(k2_zfmisc_1(k2_xboole_0(X19,X20),X21)=k2_xboole_0(k2_zfmisc_1(X19,X21),k2_zfmisc_1(X20,X21))&k2_zfmisc_1(X21,k2_xboole_0(X19,X20))=k2_xboole_0(k2_zfmisc_1(X21,X19),k2_zfmisc_1(X21,X20))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 0.95/1.14  cnf(c_0_24, negated_conjecture, (k2_xboole_0(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))=k2_zfmisc_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_13, c_0_19])).
% 0.95/1.14  cnf(c_0_25, plain, (r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3)))), inference(spm,[status(thm)],[c_0_17, c_0_20])).
% 0.95/1.14  cnf(c_0_26, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_13, c_0_20])).
% 0.95/1.14  cnf(c_0_27, negated_conjecture, (r1_tarski(esk2_0,k2_xboole_0(k2_xboole_0(k2_zfmisc_1(esk5_0,esk6_0),X1),X2))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.95/1.14  cnf(c_0_28, plain, (k2_zfmisc_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.95/1.14  cnf(c_0_29, negated_conjecture, (r1_tarski(esk1_0,X1)|~r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_17, c_0_24])).
% 0.95/1.14  cnf(c_0_30, plain, (r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1)))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.95/1.14  fof(c_0_31, plain, ![X16, X17, X18]:(~r1_tarski(X16,X17)|~r1_tarski(X18,X17)|r1_tarski(k2_xboole_0(X16,X18),X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.95/1.14  cnf(c_0_32, negated_conjecture, (r1_tarski(esk2_0,k2_xboole_0(k2_zfmisc_1(esk5_0,k2_xboole_0(esk6_0,X1)),X2))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.95/1.14  cnf(c_0_33, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.95/1.14  cnf(c_0_34, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(X1,k2_xboole_0(X2,k2_zfmisc_1(esk3_0,esk4_0))))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.95/1.14  cnf(c_0_35, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.95/1.14  cnf(c_0_36, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(k2_xboole_0(esk5_0,X1),k2_xboole_0(esk6_0,X2)))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.95/1.14  cnf(c_0_37, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(X1,k2_zfmisc_1(esk3_0,k2_xboole_0(X2,esk4_0))))), inference(spm,[status(thm)],[c_0_34, c_0_28])).
% 0.95/1.14  cnf(c_0_38, negated_conjecture, (~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.95/1.14  cnf(c_0_39, negated_conjecture, (r1_tarski(k2_xboole_0(X1,esk2_0),k2_zfmisc_1(k2_xboole_0(esk5_0,X2),k2_xboole_0(esk6_0,X3)))|~r1_tarski(X1,k2_zfmisc_1(k2_xboole_0(esk5_0,X2),k2_xboole_0(esk6_0,X3)))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.95/1.14  cnf(c_0_40, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(k2_xboole_0(X1,esk3_0),k2_xboole_0(X2,esk4_0)))), inference(spm,[status(thm)],[c_0_37, c_0_33])).
% 0.95/1.14  cnf(c_0_41, negated_conjecture, (~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk6_0,esk4_0)))), inference(rw,[status(thm)],[c_0_38, c_0_16])).
% 0.95/1.14  cnf(c_0_42, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_16]), c_0_41]), ['proof']).
% 0.95/1.14  # SZS output end CNFRefutation
% 0.95/1.14  # Proof object total steps             : 43
% 0.95/1.14  # Proof object clause steps            : 28
% 0.95/1.14  # Proof object formula steps           : 15
% 0.95/1.14  # Proof object conjectures             : 19
% 0.95/1.14  # Proof object clause conjectures      : 16
% 0.95/1.14  # Proof object formula conjectures     : 3
% 0.95/1.14  # Proof object initial clauses used    : 10
% 0.95/1.14  # Proof object initial formulas used   : 7
% 0.95/1.14  # Proof object generating inferences   : 17
% 0.95/1.14  # Proof object simplifying inferences  : 3
% 0.95/1.14  # Training examples: 0 positive, 0 negative
% 0.95/1.14  # Parsed axioms                        : 7
% 0.95/1.14  # Removed by relevancy pruning/SinE    : 0
% 0.95/1.14  # Initial clauses                      : 10
% 0.95/1.14  # Removed in clause preprocessing      : 0
% 0.95/1.14  # Initial clauses in saturation        : 10
% 0.95/1.14  # Processed clauses                    : 4811
% 0.95/1.14  # ...of these trivial                  : 3288
% 0.95/1.14  # ...subsumed                          : 419
% 0.95/1.14  # ...remaining for further processing  : 1103
% 0.95/1.14  # Other redundant clauses eliminated   : 0
% 0.95/1.14  # Clauses deleted for lack of memory   : 0
% 0.95/1.14  # Backward-subsumed                    : 0
% 0.95/1.14  # Backward-rewritten                   : 118
% 0.95/1.14  # Generated clauses                    : 138030
% 0.95/1.14  # ...of the previous two non-trivial   : 63195
% 0.95/1.14  # Contextual simplify-reflections      : 0
% 0.95/1.14  # Paramodulations                      : 138030
% 0.95/1.14  # Factorizations                       : 0
% 0.95/1.14  # Equation resolutions                 : 0
% 0.95/1.14  # Propositional unsat checks           : 0
% 0.95/1.14  #    Propositional check models        : 0
% 0.95/1.14  #    Propositional check unsatisfiable : 0
% 0.95/1.14  #    Propositional clauses             : 0
% 0.95/1.14  #    Propositional clauses after purity: 0
% 0.95/1.14  #    Propositional unsat core size     : 0
% 0.95/1.14  #    Propositional preprocessing time  : 0.000
% 0.95/1.14  #    Propositional encoding time       : 0.000
% 0.95/1.14  #    Propositional solver time         : 0.000
% 0.95/1.14  #    Success case prop preproc time    : 0.000
% 0.95/1.14  #    Success case prop encoding time   : 0.000
% 0.95/1.14  #    Success case prop solver time     : 0.000
% 0.95/1.14  # Current number of processed clauses  : 975
% 0.95/1.14  #    Positive orientable unit clauses  : 848
% 0.95/1.14  #    Positive unorientable unit clauses: 3
% 0.95/1.14  #    Negative unit clauses             : 1
% 0.95/1.14  #    Non-unit-clauses                  : 123
% 0.95/1.14  # Current number of unprocessed clauses: 57876
% 0.95/1.14  # ...number of literals in the above   : 66025
% 0.95/1.14  # Current number of archived formulas  : 0
% 0.95/1.14  # Current number of archived clauses   : 128
% 0.95/1.14  # Clause-clause subsumption calls (NU) : 6018
% 0.95/1.14  # Rec. Clause-clause subsumption calls : 6018
% 0.95/1.14  # Non-unit clause-clause subsumptions  : 387
% 0.95/1.14  # Unit Clause-clause subsumption calls : 1166
% 0.95/1.14  # Rewrite failures with RHS unbound    : 0
% 0.95/1.14  # BW rewrite match attempts            : 6283
% 0.95/1.14  # BW rewrite match successes           : 116
% 0.95/1.14  # Condensation attempts                : 0
% 0.95/1.14  # Condensation successes               : 0
% 0.95/1.14  # Termbank termtop insertions          : 1704422
% 0.95/1.15  
% 0.95/1.15  # -------------------------------------------------
% 0.95/1.15  # User time                : 0.767 s
% 0.95/1.15  # System time              : 0.031 s
% 0.95/1.15  # Total time               : 0.798 s
% 0.95/1.15  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
