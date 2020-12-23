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
% DateTime   : Thu Dec  3 10:44:26 EST 2020

% Result     : Theorem 0.75s
% Output     : CNFRefutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 104 expanded)
%              Number of clauses        :   26 (  45 expanded)
%              Number of leaves         :    8 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   69 ( 155 expanded)
%              Number of equality atoms :   20 (  73 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t143_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
        & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
     => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

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

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
          & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
       => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    inference(assume_negation,[status(cth)],[t143_zfmisc_1])).

fof(c_0_9,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(k4_xboole_0(X14,X15),X16)
      | r1_tarski(X14,k2_xboole_0(X15,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

fof(c_0_10,plain,(
    ! [X19,X20] : k3_tarski(k2_tarski(X19,X20)) = k2_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X7,X8] :
      ( ( k4_xboole_0(X7,X8) != k1_xboole_0
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | k4_xboole_0(X7,X8) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_12,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))
    & r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))
    & ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X13] : r1_tarski(k1_xboole_0,X13) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_18,plain,(
    ! [X21,X22,X23] :
      ( k2_zfmisc_1(k2_xboole_0(X21,X22),X23) = k2_xboole_0(k2_zfmisc_1(X21,X23),k2_zfmisc_1(X22,X23))
      & k2_zfmisc_1(X23,k2_xboole_0(X21,X22)) = k2_xboole_0(k2_zfmisc_1(X23,X21),k2_zfmisc_1(X23,X22)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,plain,(
    ! [X9,X10,X11,X12] :
      ( ~ r1_tarski(X9,X10)
      | ~ r1_tarski(X11,X12)
      | r1_tarski(k2_xboole_0(X9,X11),k2_xboole_0(X10,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_xboole_1])])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_zfmisc_1(esk3_0,esk4_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_19])).

fof(c_0_26,plain,(
    ! [X17,X18] : k2_tarski(X17,X18) = k2_tarski(X18,X17) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_27,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk2_0,k3_tarski(k2_tarski(k2_zfmisc_1(esk5_0,esk6_0),X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(X1,k3_tarski(k2_tarski(X2,X3))) = k3_tarski(k2_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_14]),c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk1_0,k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_25]),c_0_23])])).

cnf(c_0_31,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X3)),k3_tarski(k2_tarski(X2,X4)))
    | ~ r1_tarski(X3,X4)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_14]),c_0_14])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(esk6_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk1_0,k3_tarski(k2_tarski(X1,k2_zfmisc_1(esk3_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(X1,esk2_0)),k3_tarski(k2_tarski(X2,k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(esk6_0,X3))))))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(X1,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_29])).

cnf(c_0_37,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_38,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(esk1_0,esk2_0)),k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(X1,esk4_0))),k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(esk6_0,X2)))))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,plain,
    ( k2_zfmisc_1(k3_tarski(k2_tarski(X1,X2)),X3) = k3_tarski(k2_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_14]),c_0_14])).

cnf(c_0_41,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k2_tarski(esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk4_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_14]),c_0_14]),c_0_14])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_31]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:34:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.75/0.93  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.75/0.93  # and selection function SelectDiffNegLit.
% 0.75/0.93  #
% 0.75/0.93  # Preprocessing time       : 0.026 s
% 0.75/0.93  # Presaturation interreduction done
% 0.75/0.93  
% 0.75/0.93  # Proof found!
% 0.75/0.93  # SZS status Theorem
% 0.75/0.93  # SZS output start CNFRefutation
% 0.75/0.93  fof(t143_zfmisc_1, conjecture, ![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 0.75/0.93  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.75/0.93  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.75/0.93  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.75/0.93  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.75/0.93  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 0.75/0.93  fof(t13_xboole_1, axiom, ![X1, X2, X3, X4]:((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_xboole_1)).
% 0.75/0.93  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.75/0.93  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))))), inference(assume_negation,[status(cth)],[t143_zfmisc_1])).
% 0.75/0.93  fof(c_0_9, plain, ![X14, X15, X16]:(~r1_tarski(k4_xboole_0(X14,X15),X16)|r1_tarski(X14,k2_xboole_0(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.75/0.93  fof(c_0_10, plain, ![X19, X20]:k3_tarski(k2_tarski(X19,X20))=k2_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.75/0.93  fof(c_0_11, plain, ![X7, X8]:((k4_xboole_0(X7,X8)!=k1_xboole_0|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|k4_xboole_0(X7,X8)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.75/0.93  fof(c_0_12, negated_conjecture, ((r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))&r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)))&~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.75/0.93  cnf(c_0_13, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.75/0.93  cnf(c_0_14, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.75/0.93  cnf(c_0_15, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.75/0.93  cnf(c_0_16, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.75/0.93  fof(c_0_17, plain, ![X13]:r1_tarski(k1_xboole_0,X13), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.75/0.93  fof(c_0_18, plain, ![X21, X22, X23]:(k2_zfmisc_1(k2_xboole_0(X21,X22),X23)=k2_xboole_0(k2_zfmisc_1(X21,X23),k2_zfmisc_1(X22,X23))&k2_zfmisc_1(X23,k2_xboole_0(X21,X22))=k2_xboole_0(k2_zfmisc_1(X23,X21),k2_zfmisc_1(X23,X22))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 0.75/0.93  cnf(c_0_19, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.75/0.93  fof(c_0_20, plain, ![X9, X10, X11, X12]:(~r1_tarski(X9,X10)|~r1_tarski(X11,X12)|r1_tarski(k2_xboole_0(X9,X11),k2_xboole_0(X10,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_xboole_1])])).
% 0.75/0.93  cnf(c_0_21, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.75/0.93  cnf(c_0_22, negated_conjecture, (k4_xboole_0(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.75/0.93  cnf(c_0_23, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.75/0.93  cnf(c_0_24, plain, (k2_zfmisc_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.75/0.93  cnf(c_0_25, negated_conjecture, (k4_xboole_0(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_15, c_0_19])).
% 0.75/0.93  fof(c_0_26, plain, ![X17, X18]:k2_tarski(X17,X18)=k2_tarski(X18,X17), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.75/0.93  cnf(c_0_27, plain, (r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.75/0.93  cnf(c_0_28, negated_conjecture, (r1_tarski(esk2_0,k3_tarski(k2_tarski(k2_zfmisc_1(esk5_0,esk6_0),X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.75/0.93  cnf(c_0_29, plain, (k2_zfmisc_1(X1,k3_tarski(k2_tarski(X2,X3)))=k3_tarski(k2_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_14]), c_0_14])).
% 0.75/0.93  cnf(c_0_30, negated_conjecture, (r1_tarski(esk1_0,k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_25]), c_0_23])])).
% 0.75/0.93  cnf(c_0_31, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.75/0.93  cnf(c_0_32, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X3)),k3_tarski(k2_tarski(X2,X4)))|~r1_tarski(X3,X4)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_14]), c_0_14])).
% 0.75/0.93  cnf(c_0_33, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(esk6_0,X1))))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.75/0.93  cnf(c_0_34, negated_conjecture, (r1_tarski(esk1_0,k3_tarski(k2_tarski(X1,k2_zfmisc_1(esk3_0,esk4_0))))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.75/0.93  cnf(c_0_35, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(X1,esk2_0)),k3_tarski(k2_tarski(X2,k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(esk6_0,X3))))))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.75/0.93  cnf(c_0_36, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(X1,esk4_0))))), inference(spm,[status(thm)],[c_0_34, c_0_29])).
% 0.75/0.93  cnf(c_0_37, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.75/0.93  cnf(c_0_38, negated_conjecture, (~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.75/0.93  cnf(c_0_39, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(esk1_0,esk2_0)),k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(X1,esk4_0))),k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(esk6_0,X2))))))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.75/0.93  cnf(c_0_40, plain, (k2_zfmisc_1(k3_tarski(k2_tarski(X1,X2)),X3)=k3_tarski(k2_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_14]), c_0_14])).
% 0.75/0.93  cnf(c_0_41, negated_conjecture, (~r1_tarski(k3_tarski(k2_tarski(esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk4_0,esk6_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_14]), c_0_14]), c_0_14])).
% 0.75/0.93  cnf(c_0_42, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_31]), c_0_41]), ['proof']).
% 0.75/0.93  # SZS output end CNFRefutation
% 0.75/0.93  # Proof object total steps             : 43
% 0.75/0.93  # Proof object clause steps            : 26
% 0.75/0.93  # Proof object formula steps           : 17
% 0.75/0.93  # Proof object conjectures             : 17
% 0.75/0.93  # Proof object clause conjectures      : 14
% 0.75/0.93  # Proof object formula conjectures     : 3
% 0.75/0.93  # Proof object initial clauses used    : 11
% 0.75/0.93  # Proof object initial formulas used   : 8
% 0.75/0.93  # Proof object generating inferences   : 10
% 0.75/0.93  # Proof object simplifying inferences  : 16
% 0.75/0.93  # Training examples: 0 positive, 0 negative
% 0.75/0.93  # Parsed axioms                        : 8
% 0.75/0.93  # Removed by relevancy pruning/SinE    : 0
% 0.75/0.93  # Initial clauses                      : 12
% 0.75/0.93  # Removed in clause preprocessing      : 1
% 0.75/0.93  # Initial clauses in saturation        : 11
% 0.75/0.93  # Processed clauses                    : 1811
% 0.75/0.93  # ...of these trivial                  : 925
% 0.75/0.93  # ...subsumed                          : 5
% 0.75/0.93  # ...remaining for further processing  : 880
% 0.75/0.93  # Other redundant clauses eliminated   : 0
% 0.75/0.93  # Clauses deleted for lack of memory   : 0
% 0.75/0.93  # Backward-subsumed                    : 0
% 0.75/0.93  # Backward-rewritten                   : 61
% 0.75/0.93  # Generated clauses                    : 67481
% 0.75/0.93  # ...of the previous two non-trivial   : 63400
% 0.75/0.93  # Contextual simplify-reflections      : 0
% 0.75/0.93  # Paramodulations                      : 67481
% 0.75/0.93  # Factorizations                       : 0
% 0.75/0.93  # Equation resolutions                 : 0
% 0.75/0.93  # Propositional unsat checks           : 0
% 0.75/0.93  #    Propositional check models        : 0
% 0.75/0.93  #    Propositional check unsatisfiable : 0
% 0.75/0.93  #    Propositional clauses             : 0
% 0.75/0.93  #    Propositional clauses after purity: 0
% 0.75/0.93  #    Propositional unsat core size     : 0
% 0.75/0.93  #    Propositional preprocessing time  : 0.000
% 0.75/0.93  #    Propositional encoding time       : 0.000
% 0.75/0.93  #    Propositional solver time         : 0.000
% 0.75/0.93  #    Success case prop preproc time    : 0.000
% 0.75/0.93  #    Success case prop encoding time   : 0.000
% 0.75/0.93  #    Success case prop solver time     : 0.000
% 0.75/0.93  # Current number of processed clauses  : 808
% 0.75/0.93  #    Positive orientable unit clauses  : 695
% 0.75/0.93  #    Positive unorientable unit clauses: 11
% 0.75/0.93  #    Negative unit clauses             : 1
% 0.75/0.93  #    Non-unit-clauses                  : 101
% 0.75/0.93  # Current number of unprocessed clauses: 61518
% 0.75/0.93  # ...number of literals in the above   : 62033
% 0.75/0.93  # Current number of archived formulas  : 0
% 0.75/0.93  # Current number of archived clauses   : 73
% 0.75/0.93  # Clause-clause subsumption calls (NU) : 2773
% 0.75/0.93  # Rec. Clause-clause subsumption calls : 2773
% 0.75/0.93  # Non-unit clause-clause subsumptions  : 0
% 0.75/0.93  # Unit Clause-clause subsumption calls : 4682
% 0.75/0.93  # Rewrite failures with RHS unbound    : 0
% 0.75/0.93  # BW rewrite match attempts            : 59081
% 0.75/0.93  # BW rewrite match successes           : 99
% 0.75/0.93  # Condensation attempts                : 0
% 0.75/0.93  # Condensation successes               : 0
% 0.75/0.93  # Termbank termtop insertions          : 2150704
% 0.79/0.93  
% 0.79/0.93  # -------------------------------------------------
% 0.79/0.93  # User time                : 0.563 s
% 0.79/0.93  # System time              : 0.030 s
% 0.79/0.93  # Total time               : 0.593 s
% 0.79/0.93  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
