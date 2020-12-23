%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:27 EST 2020

% Result     : Theorem 0.53s
% Output     : CNFRefutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 118 expanded)
%              Number of clauses        :   24 (  51 expanded)
%              Number of leaves         :    7 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   57 ( 169 expanded)
%              Number of equality atoms :   18 (  83 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t13_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t143_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
        & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
     => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(c_0_7,plain,(
    ! [X7,X8,X9,X10] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X9,X10)
      | r1_tarski(k2_xboole_0(X7,X9),k2_xboole_0(X8,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_xboole_1])])).

fof(c_0_8,plain,(
    ! [X15,X16] : k3_tarski(k2_tarski(X15,X16)) = k2_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_9,plain,(
    ! [X11] : k2_xboole_0(X11,k1_xboole_0) = X11 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_10,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X12] : r1_tarski(k1_xboole_0,X12) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
          & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
       => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    inference(assume_negation,[status(cth)],[t143_zfmisc_1])).

cnf(c_0_15,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X3)),k3_tarski(k2_tarski(X2,X4)))
    | ~ r1_tarski(X3,X4)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_11]),c_0_11])).

cnf(c_0_16,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k3_tarski(k2_tarski(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_13,c_0_11])).

fof(c_0_18,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))
    & r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))
    & ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_19,plain,(
    ! [X17,X18,X19] :
      ( k2_zfmisc_1(k2_xboole_0(X17,X18),X19) = k2_xboole_0(k2_zfmisc_1(X17,X19),k2_zfmisc_1(X18,X19))
      & k2_zfmisc_1(X19,k2_xboole_0(X17,X18)) = k2_xboole_0(k2_zfmisc_1(X19,X17),k2_zfmisc_1(X19,X18)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X13,X14] : k2_tarski(X13,X14) = k2_tarski(X14,X13) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk2_0,k3_tarski(k2_tarski(k2_zfmisc_1(esk5_0,esk6_0),X1))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( k2_zfmisc_1(X1,k3_tarski(k2_tarski(X2,X3))) = k3_tarski(k2_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_11]),c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk1_0,k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_23])).

cnf(c_0_28,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(esk6_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk1_0,k3_tarski(k2_tarski(X1,k2_zfmisc_1(esk3_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(X1,esk2_0)),k3_tarski(k2_tarski(X2,k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(esk6_0,X3))))))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(X1,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_26])).

cnf(c_0_33,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(esk1_0,esk2_0)),k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(X1,esk4_0))),k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(esk6_0,X2)))))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(k3_tarski(k2_tarski(X1,X2)),X3) = k3_tarski(k2_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_11]),c_0_11])).

cnf(c_0_37,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k2_tarski(esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk4_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_11]),c_0_11]),c_0_11])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_28]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.36  % Computer   : n023.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 20:50:05 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  # Version: 2.5pre002
% 0.15/0.36  # No SInE strategy applied
% 0.15/0.36  # Trying AutoSched0 for 299 seconds
% 0.53/0.68  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.53/0.68  # and selection function SelectDiffNegLit.
% 0.53/0.68  #
% 0.53/0.68  # Preprocessing time       : 0.026 s
% 0.53/0.68  # Presaturation interreduction done
% 0.53/0.68  
% 0.53/0.68  # Proof found!
% 0.53/0.68  # SZS status Theorem
% 0.53/0.68  # SZS output start CNFRefutation
% 0.53/0.68  fof(t13_xboole_1, axiom, ![X1, X2, X3, X4]:((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_xboole_1)).
% 0.53/0.68  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.53/0.68  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.53/0.68  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.53/0.68  fof(t143_zfmisc_1, conjecture, ![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 0.53/0.68  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 0.53/0.68  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.53/0.68  fof(c_0_7, plain, ![X7, X8, X9, X10]:(~r1_tarski(X7,X8)|~r1_tarski(X9,X10)|r1_tarski(k2_xboole_0(X7,X9),k2_xboole_0(X8,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_xboole_1])])).
% 0.53/0.68  fof(c_0_8, plain, ![X15, X16]:k3_tarski(k2_tarski(X15,X16))=k2_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.53/0.68  fof(c_0_9, plain, ![X11]:k2_xboole_0(X11,k1_xboole_0)=X11, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.53/0.68  cnf(c_0_10, plain, (r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.53/0.68  cnf(c_0_11, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.53/0.68  fof(c_0_12, plain, ![X12]:r1_tarski(k1_xboole_0,X12), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.53/0.68  cnf(c_0_13, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.53/0.68  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))))), inference(assume_negation,[status(cth)],[t143_zfmisc_1])).
% 0.53/0.68  cnf(c_0_15, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X3)),k3_tarski(k2_tarski(X2,X4)))|~r1_tarski(X3,X4)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10, c_0_11]), c_0_11])).
% 0.53/0.68  cnf(c_0_16, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.53/0.68  cnf(c_0_17, plain, (k3_tarski(k2_tarski(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_13, c_0_11])).
% 0.53/0.68  fof(c_0_18, negated_conjecture, ((r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))&r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)))&~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.53/0.68  fof(c_0_19, plain, ![X17, X18, X19]:(k2_zfmisc_1(k2_xboole_0(X17,X18),X19)=k2_xboole_0(k2_zfmisc_1(X17,X19),k2_zfmisc_1(X18,X19))&k2_zfmisc_1(X19,k2_xboole_0(X17,X18))=k2_xboole_0(k2_zfmisc_1(X19,X17),k2_zfmisc_1(X19,X18))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 0.53/0.68  cnf(c_0_20, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 0.53/0.68  cnf(c_0_21, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.53/0.68  cnf(c_0_22, plain, (k2_zfmisc_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.53/0.68  cnf(c_0_23, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.53/0.68  fof(c_0_24, plain, ![X13, X14]:k2_tarski(X13,X14)=k2_tarski(X14,X13), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.53/0.68  cnf(c_0_25, negated_conjecture, (r1_tarski(esk2_0,k3_tarski(k2_tarski(k2_zfmisc_1(esk5_0,esk6_0),X1)))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.53/0.68  cnf(c_0_26, plain, (k2_zfmisc_1(X1,k3_tarski(k2_tarski(X2,X3)))=k3_tarski(k2_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_11]), c_0_11])).
% 0.53/0.68  cnf(c_0_27, negated_conjecture, (r1_tarski(esk1_0,k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1)))), inference(spm,[status(thm)],[c_0_20, c_0_23])).
% 0.53/0.68  cnf(c_0_28, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.53/0.68  cnf(c_0_29, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(esk6_0,X1))))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.53/0.68  cnf(c_0_30, negated_conjecture, (r1_tarski(esk1_0,k3_tarski(k2_tarski(X1,k2_zfmisc_1(esk3_0,esk4_0))))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.53/0.68  cnf(c_0_31, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(X1,esk2_0)),k3_tarski(k2_tarski(X2,k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(esk6_0,X3))))))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_15, c_0_29])).
% 0.53/0.68  cnf(c_0_32, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(X1,esk4_0))))), inference(spm,[status(thm)],[c_0_30, c_0_26])).
% 0.53/0.68  cnf(c_0_33, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.53/0.68  cnf(c_0_34, negated_conjecture, (~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.53/0.68  cnf(c_0_35, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(esk1_0,esk2_0)),k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(X1,esk4_0))),k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(esk6_0,X2))))))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.53/0.68  cnf(c_0_36, plain, (k2_zfmisc_1(k3_tarski(k2_tarski(X1,X2)),X3)=k3_tarski(k2_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_11]), c_0_11])).
% 0.53/0.68  cnf(c_0_37, negated_conjecture, (~r1_tarski(k3_tarski(k2_tarski(esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk4_0,esk6_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_11]), c_0_11]), c_0_11])).
% 0.53/0.68  cnf(c_0_38, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_28]), c_0_37]), ['proof']).
% 0.53/0.68  # SZS output end CNFRefutation
% 0.53/0.68  # Proof object total steps             : 39
% 0.53/0.68  # Proof object clause steps            : 24
% 0.53/0.68  # Proof object formula steps           : 15
% 0.53/0.68  # Proof object conjectures             : 15
% 0.53/0.68  # Proof object clause conjectures      : 12
% 0.53/0.68  # Proof object formula conjectures     : 3
% 0.53/0.68  # Proof object initial clauses used    : 10
% 0.53/0.68  # Proof object initial formulas used   : 7
% 0.53/0.68  # Proof object generating inferences   : 9
% 0.53/0.68  # Proof object simplifying inferences  : 13
% 0.53/0.68  # Training examples: 0 positive, 0 negative
% 0.53/0.68  # Parsed axioms                        : 7
% 0.53/0.68  # Removed by relevancy pruning/SinE    : 0
% 0.53/0.68  # Initial clauses                      : 10
% 0.53/0.68  # Removed in clause preprocessing      : 1
% 0.53/0.68  # Initial clauses in saturation        : 9
% 0.53/0.68  # Processed clauses                    : 920
% 0.53/0.68  # ...of these trivial                  : 414
% 0.53/0.68  # ...subsumed                          : 4
% 0.53/0.68  # ...remaining for further processing  : 501
% 0.53/0.68  # Other redundant clauses eliminated   : 0
% 0.53/0.68  # Clauses deleted for lack of memory   : 0
% 0.53/0.68  # Backward-subsumed                    : 0
% 0.53/0.68  # Backward-rewritten                   : 10
% 0.53/0.68  # Generated clauses                    : 30747
% 0.53/0.68  # ...of the previous two non-trivial   : 28475
% 0.53/0.68  # Contextual simplify-reflections      : 0
% 0.53/0.68  # Paramodulations                      : 30747
% 0.53/0.68  # Factorizations                       : 0
% 0.53/0.68  # Equation resolutions                 : 0
% 0.53/0.68  # Propositional unsat checks           : 0
% 0.53/0.68  #    Propositional check models        : 0
% 0.53/0.68  #    Propositional check unsatisfiable : 0
% 0.53/0.68  #    Propositional clauses             : 0
% 0.53/0.68  #    Propositional clauses after purity: 0
% 0.53/0.68  #    Propositional unsat core size     : 0
% 0.53/0.68  #    Propositional preprocessing time  : 0.000
% 0.53/0.68  #    Propositional encoding time       : 0.000
% 0.53/0.68  #    Propositional solver time         : 0.000
% 0.53/0.68  #    Success case prop preproc time    : 0.000
% 0.53/0.68  #    Success case prop encoding time   : 0.000
% 0.53/0.68  #    Success case prop solver time     : 0.000
% 0.53/0.68  # Current number of processed clauses  : 482
% 0.53/0.68  #    Positive orientable unit clauses  : 412
% 0.53/0.68  #    Positive unorientable unit clauses: 2
% 0.53/0.68  #    Negative unit clauses             : 1
% 0.53/0.68  #    Non-unit-clauses                  : 67
% 0.53/0.68  # Current number of unprocessed clauses: 27562
% 0.53/0.68  # ...number of literals in the above   : 27904
% 0.53/0.68  # Current number of archived formulas  : 0
% 0.53/0.68  # Current number of archived clauses   : 20
% 0.53/0.68  # Clause-clause subsumption calls (NU) : 1702
% 0.53/0.68  # Rec. Clause-clause subsumption calls : 1702
% 0.53/0.68  # Non-unit clause-clause subsumptions  : 0
% 0.53/0.68  # Unit Clause-clause subsumption calls : 2349
% 0.53/0.68  # Rewrite failures with RHS unbound    : 0
% 0.53/0.68  # BW rewrite match attempts            : 25304
% 0.53/0.68  # BW rewrite match successes           : 28
% 0.53/0.68  # Condensation attempts                : 0
% 0.53/0.68  # Condensation successes               : 0
% 0.53/0.68  # Termbank termtop insertions          : 935198
% 0.53/0.69  
% 0.53/0.69  # -------------------------------------------------
% 0.53/0.69  # User time                : 0.303 s
% 0.53/0.69  # System time              : 0.026 s
% 0.53/0.69  # Total time               : 0.329 s
% 0.53/0.69  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
