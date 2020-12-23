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
% DateTime   : Thu Dec  3 10:44:28 EST 2020

% Result     : Theorem 6.45s
% Output     : CNFRefutation 6.45s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 136 expanded)
%              Number of clauses        :   31 (  61 expanded)
%              Number of leaves         :    8 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :   75 ( 187 expanded)
%              Number of equality atoms :   21 (  99 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t143_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
        & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
     => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(t13_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

fof(c_0_8,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,X13)
      | k2_xboole_0(X12,X13) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_9,plain,(
    ! [X20,X21] : k3_tarski(k2_tarski(X20,X21)) = k2_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
          & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
       => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    inference(assume_negation,[status(cth)],[t143_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(k2_xboole_0(X9,X10),X11)
      | r1_tarski(X9,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_12,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))
    & r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))
    & ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X18,X19] : r1_tarski(X18,k2_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_19,plain,(
    ! [X7,X8] : k2_xboole_0(X7,X8) = k2_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k3_tarski(k2_tarski(X1,X2)),X3) ),
    inference(rw,[status(thm)],[c_0_15,c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( k3_tarski(k2_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))) = k2_zfmisc_1(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X22,X23,X24] :
      ( k2_zfmisc_1(k2_xboole_0(X22,X23),X24) = k2_xboole_0(k2_zfmisc_1(X22,X24),k2_zfmisc_1(X23,X24))
      & k2_zfmisc_1(X24,k2_xboole_0(X22,X23)) = k2_xboole_0(k2_zfmisc_1(X24,X22),k2_zfmisc_1(X24,X23)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X14,X15,X16,X17] :
      ( ~ r1_tarski(X14,X15)
      | ~ r1_tarski(X16,X17)
      | r1_tarski(k2_xboole_0(X14,X16),k2_xboole_0(X15,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_xboole_1])])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_13])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( k3_tarski(k2_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_24])).

cnf(c_0_31,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_13]),c_0_13])).

cnf(c_0_32,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk2_0,k3_tarski(k2_tarski(k2_zfmisc_1(esk5_0,esk6_0),X1))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( k2_zfmisc_1(X1,k3_tarski(k2_tarski(X2,X3))) = k3_tarski(k2_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_13]),c_0_13])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk1_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_30])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_31])).

cnf(c_0_37,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X3)),k3_tarski(k2_tarski(X2,X4)))
    | ~ r1_tarski(X3,X4)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_13]),c_0_13])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(esk6_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk1_0,k3_tarski(k2_tarski(X1,k2_zfmisc_1(esk3_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(X1,esk2_0)),k3_tarski(k2_tarski(X2,k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(esk6_0,X3))))))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(X1,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_34])).

cnf(c_0_42,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(esk1_0,esk2_0)),k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(X1,esk4_0))),k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(esk6_0,X2)))))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,plain,
    ( k2_zfmisc_1(k3_tarski(k2_tarski(X1,X2)),X3) = k3_tarski(k2_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_13]),c_0_13])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k2_tarski(esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk4_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_13]),c_0_13]),c_0_13])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_31]),c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:52:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 6.45/6.69  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 6.45/6.69  # and selection function SelectDiffNegLit.
% 6.45/6.69  #
% 6.45/6.69  # Preprocessing time       : 0.026 s
% 6.45/6.69  # Presaturation interreduction done
% 6.45/6.69  
% 6.45/6.69  # Proof found!
% 6.45/6.69  # SZS status Theorem
% 6.45/6.69  # SZS output start CNFRefutation
% 6.45/6.69  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.45/6.69  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.45/6.69  fof(t143_zfmisc_1, conjecture, ![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 6.45/6.69  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 6.45/6.69  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.45/6.69  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.45/6.69  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 6.45/6.69  fof(t13_xboole_1, axiom, ![X1, X2, X3, X4]:((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_xboole_1)).
% 6.45/6.69  fof(c_0_8, plain, ![X12, X13]:(~r1_tarski(X12,X13)|k2_xboole_0(X12,X13)=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 6.45/6.69  fof(c_0_9, plain, ![X20, X21]:k3_tarski(k2_tarski(X20,X21))=k2_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 6.45/6.69  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))))), inference(assume_negation,[status(cth)],[t143_zfmisc_1])).
% 6.45/6.69  fof(c_0_11, plain, ![X9, X10, X11]:(~r1_tarski(k2_xboole_0(X9,X10),X11)|r1_tarski(X9,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 6.45/6.69  cnf(c_0_12, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 6.45/6.69  cnf(c_0_13, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 6.45/6.69  fof(c_0_14, negated_conjecture, ((r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))&r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)))&~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 6.45/6.69  cnf(c_0_15, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 6.45/6.69  cnf(c_0_16, plain, (k3_tarski(k2_tarski(X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 6.45/6.69  cnf(c_0_17, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 6.45/6.69  fof(c_0_18, plain, ![X18, X19]:r1_tarski(X18,k2_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 6.45/6.69  fof(c_0_19, plain, ![X7, X8]:k2_xboole_0(X7,X8)=k2_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 6.45/6.69  cnf(c_0_20, plain, (r1_tarski(X1,X3)|~r1_tarski(k3_tarski(k2_tarski(X1,X2)),X3)), inference(rw,[status(thm)],[c_0_15, c_0_13])).
% 6.45/6.69  cnf(c_0_21, negated_conjecture, (k3_tarski(k2_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)))=k2_zfmisc_1(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 6.45/6.69  cnf(c_0_22, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 6.45/6.69  fof(c_0_23, plain, ![X22, X23, X24]:(k2_zfmisc_1(k2_xboole_0(X22,X23),X24)=k2_xboole_0(k2_zfmisc_1(X22,X24),k2_zfmisc_1(X23,X24))&k2_zfmisc_1(X24,k2_xboole_0(X22,X23))=k2_xboole_0(k2_zfmisc_1(X24,X22),k2_zfmisc_1(X24,X23))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 6.45/6.69  cnf(c_0_24, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 6.45/6.69  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 6.45/6.69  fof(c_0_26, plain, ![X14, X15, X16, X17]:(~r1_tarski(X14,X15)|~r1_tarski(X16,X17)|r1_tarski(k2_xboole_0(X14,X16),k2_xboole_0(X15,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_xboole_1])])).
% 6.45/6.69  cnf(c_0_27, negated_conjecture, (r1_tarski(esk2_0,X1)|~r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 6.45/6.69  cnf(c_0_28, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_22, c_0_13])).
% 6.45/6.69  cnf(c_0_29, plain, (k2_zfmisc_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 6.45/6.69  cnf(c_0_30, negated_conjecture, (k3_tarski(k2_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0)))=k2_zfmisc_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_16, c_0_24])).
% 6.45/6.69  cnf(c_0_31, plain, (k3_tarski(k2_tarski(X1,X2))=k3_tarski(k2_tarski(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_13]), c_0_13])).
% 6.45/6.69  cnf(c_0_32, plain, (r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 6.45/6.69  cnf(c_0_33, negated_conjecture, (r1_tarski(esk2_0,k3_tarski(k2_tarski(k2_zfmisc_1(esk5_0,esk6_0),X1)))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 6.45/6.69  cnf(c_0_34, plain, (k2_zfmisc_1(X1,k3_tarski(k2_tarski(X2,X3)))=k3_tarski(k2_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_13]), c_0_13])).
% 6.45/6.69  cnf(c_0_35, negated_conjecture, (r1_tarski(esk1_0,X1)|~r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_20, c_0_30])).
% 6.45/6.69  cnf(c_0_36, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X1)))), inference(spm,[status(thm)],[c_0_28, c_0_31])).
% 6.45/6.69  cnf(c_0_37, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X3)),k3_tarski(k2_tarski(X2,X4)))|~r1_tarski(X3,X4)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_13]), c_0_13])).
% 6.45/6.69  cnf(c_0_38, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(esk6_0,X1))))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 6.45/6.69  cnf(c_0_39, negated_conjecture, (r1_tarski(esk1_0,k3_tarski(k2_tarski(X1,k2_zfmisc_1(esk3_0,esk4_0))))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 6.45/6.69  cnf(c_0_40, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(X1,esk2_0)),k3_tarski(k2_tarski(X2,k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(esk6_0,X3))))))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 6.45/6.69  cnf(c_0_41, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(X1,esk4_0))))), inference(spm,[status(thm)],[c_0_39, c_0_34])).
% 6.45/6.69  cnf(c_0_42, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 6.45/6.69  cnf(c_0_43, negated_conjecture, (~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 6.45/6.69  cnf(c_0_44, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(esk1_0,esk2_0)),k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(X1,esk4_0))),k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(esk6_0,X2))))))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 6.45/6.69  cnf(c_0_45, plain, (k2_zfmisc_1(k3_tarski(k2_tarski(X1,X2)),X3)=k3_tarski(k2_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_13]), c_0_13])).
% 6.45/6.69  cnf(c_0_46, negated_conjecture, (~r1_tarski(k3_tarski(k2_tarski(esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk4_0,esk6_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_13]), c_0_13]), c_0_13])).
% 6.45/6.69  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_31]), c_0_46]), ['proof']).
% 6.45/6.69  # SZS output end CNFRefutation
% 6.45/6.69  # Proof object total steps             : 48
% 6.45/6.69  # Proof object clause steps            : 31
% 6.45/6.69  # Proof object formula steps           : 17
% 6.45/6.69  # Proof object conjectures             : 18
% 6.45/6.69  # Proof object clause conjectures      : 15
% 6.45/6.69  # Proof object formula conjectures     : 3
% 6.45/6.69  # Proof object initial clauses used    : 11
% 6.45/6.69  # Proof object initial formulas used   : 8
% 6.45/6.69  # Proof object generating inferences   : 12
% 6.45/6.69  # Proof object simplifying inferences  : 16
% 6.45/6.69  # Training examples: 0 positive, 0 negative
% 6.45/6.69  # Parsed axioms                        : 8
% 6.45/6.69  # Removed by relevancy pruning/SinE    : 0
% 6.45/6.69  # Initial clauses                      : 11
% 6.45/6.69  # Removed in clause preprocessing      : 1
% 6.45/6.69  # Initial clauses in saturation        : 10
% 6.45/6.69  # Processed clauses                    : 18123
% 6.45/6.69  # ...of these trivial                  : 5060
% 6.45/6.69  # ...subsumed                          : 7646
% 6.45/6.69  # ...remaining for further processing  : 5417
% 6.45/6.69  # Other redundant clauses eliminated   : 0
% 6.45/6.69  # Clauses deleted for lack of memory   : 0
% 6.45/6.69  # Backward-subsumed                    : 26
% 6.45/6.69  # Backward-rewritten                   : 554
% 6.45/6.69  # Generated clauses                    : 773697
% 6.45/6.69  # ...of the previous two non-trivial   : 634488
% 6.45/6.69  # Contextual simplify-reflections      : 0
% 6.45/6.69  # Paramodulations                      : 773697
% 6.45/6.69  # Factorizations                       : 0
% 6.45/6.69  # Equation resolutions                 : 0
% 6.45/6.69  # Propositional unsat checks           : 0
% 6.45/6.69  #    Propositional check models        : 0
% 6.45/6.69  #    Propositional check unsatisfiable : 0
% 6.45/6.69  #    Propositional clauses             : 0
% 6.45/6.69  #    Propositional clauses after purity: 0
% 6.45/6.69  #    Propositional unsat core size     : 0
% 6.45/6.69  #    Propositional preprocessing time  : 0.000
% 6.45/6.69  #    Propositional encoding time       : 0.000
% 6.45/6.69  #    Propositional solver time         : 0.000
% 6.45/6.69  #    Success case prop preproc time    : 0.000
% 6.45/6.69  #    Success case prop encoding time   : 0.000
% 6.45/6.69  #    Success case prop solver time     : 0.000
% 6.45/6.69  # Current number of processed clauses  : 4827
% 6.45/6.69  #    Positive orientable unit clauses  : 4266
% 6.45/6.69  #    Positive unorientable unit clauses: 10
% 6.45/6.69  #    Negative unit clauses             : 1
% 6.45/6.69  #    Non-unit-clauses                  : 550
% 6.45/6.69  # Current number of unprocessed clauses: 614854
% 6.45/6.69  # ...number of literals in the above   : 637798
% 6.45/6.69  # Current number of archived formulas  : 0
% 6.45/6.69  # Current number of archived clauses   : 591
% 6.45/6.69  # Clause-clause subsumption calls (NU) : 284535
% 6.45/6.69  # Rec. Clause-clause subsumption calls : 283622
% 6.45/6.69  # Non-unit clause-clause subsumptions  : 7616
% 6.45/6.69  # Unit Clause-clause subsumption calls : 12534
% 6.45/6.69  # Rewrite failures with RHS unbound    : 0
% 6.45/6.69  # BW rewrite match attempts            : 931961
% 6.45/6.69  # BW rewrite match successes           : 631
% 6.45/6.69  # Condensation attempts                : 0
% 6.45/6.69  # Condensation successes               : 0
% 6.45/6.69  # Termbank termtop insertions          : 23585003
% 6.55/6.72  
% 6.55/6.72  # -------------------------------------------------
% 6.55/6.72  # User time                : 6.078 s
% 6.55/6.72  # System time              : 0.299 s
% 6.55/6.72  # Total time               : 6.377 s
% 6.55/6.72  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
