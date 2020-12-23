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
% DateTime   : Thu Dec  3 10:44:26 EST 2020

% Result     : Theorem 44.98s
% Output     : CNFRefutation 44.98s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 164 expanded)
%              Number of clauses        :   27 (  75 expanded)
%              Number of leaves         :    8 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :   68 ( 211 expanded)
%              Number of equality atoms :   19 ( 129 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t143_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
        & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
     => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(t13_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(c_0_8,plain,(
    ! [X30,X31] : k3_tarski(k2_tarski(X30,X31)) = k2_xboole_0(X30,X31) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_9,plain,(
    ! [X28,X29] : k1_enumset1(X28,X28,X29) = k2_tarski(X28,X29) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_10,plain,(
    ! [X24,X25] : r1_tarski(X24,k2_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_11,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X15,X16,X17] :
      ( ~ r1_tarski(X15,X16)
      | ~ r1_tarski(X16,X17)
      | r1_tarski(X15,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
          & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
       => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    inference(assume_negation,[status(cth)],[t143_zfmisc_1])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_19,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))
    & r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))
    & ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_20,plain,(
    ! [X32,X33,X34] :
      ( k2_zfmisc_1(k2_xboole_0(X32,X33),X34) = k2_xboole_0(k2_zfmisc_1(X32,X34),k2_zfmisc_1(X33,X34))
      & k2_zfmisc_1(X34,k2_xboole_0(X32,X33)) = k2_xboole_0(k2_zfmisc_1(X34,X32),k2_zfmisc_1(X34,X33)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X11,X12,X13,X14] :
      ( ~ r1_tarski(X11,X12)
      | ~ r1_tarski(X13,X14)
      | r1_tarski(k2_xboole_0(X11,X13),k2_xboole_0(X12,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_xboole_1])])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X26,X27] : k2_tarski(X26,X27) = k2_tarski(X27,X26) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_27,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk2_0,k3_tarski(k1_enumset1(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk5_0,esk6_0),X1))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(X1,k3_tarski(k1_enumset1(X2,X2,X3))) = k3_tarski(k1_enumset1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_15]),c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk1_0,k3_tarski(k1_enumset1(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),X1))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_25])).

cnf(c_0_31,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),k3_tarski(k1_enumset1(X2,X2,X4)))
    | ~ r1_tarski(X3,X4)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_15]),c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(esk6_0,esk6_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(esk4_0,esk4_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_35,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_12]),c_0_12])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k3_tarski(k1_enumset1(X1,X1,esk2_0)),k3_tarski(k1_enumset1(X2,X2,k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(esk6_0,esk6_0,X3))))))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(X1,X1,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_39,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k3_tarski(k1_enumset1(esk1_0,esk1_0,esk2_0)),k3_tarski(k1_enumset1(k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(X1,X1,esk4_0))),k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(X1,X1,esk4_0))),k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(esk6_0,esk6_0,X2)))))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( k2_zfmisc_1(k3_tarski(k1_enumset1(X1,X1,X2)),X3) = k3_tarski(k1_enumset1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_15]),c_0_15])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k1_enumset1(esk1_0,esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k1_enumset1(esk3_0,esk3_0,esk5_0)),k3_tarski(k1_enumset1(esk4_0,esk4_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_15]),c_0_15]),c_0_15])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_35]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:53:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 44.98/45.29  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S081N
% 44.98/45.29  # and selection function SelectCQArNTNp.
% 44.98/45.29  #
% 44.98/45.29  # Preprocessing time       : 0.027 s
% 44.98/45.29  # Presaturation interreduction done
% 44.98/45.29  
% 44.98/45.29  # Proof found!
% 44.98/45.29  # SZS status Theorem
% 44.98/45.29  # SZS output start CNFRefutation
% 44.98/45.29  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 44.98/45.29  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 44.98/45.29  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 44.98/45.29  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 44.98/45.29  fof(t143_zfmisc_1, conjecture, ![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 44.98/45.29  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 44.98/45.29  fof(t13_xboole_1, axiom, ![X1, X2, X3, X4]:((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_xboole_1)).
% 44.98/45.29  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 44.98/45.29  fof(c_0_8, plain, ![X30, X31]:k3_tarski(k2_tarski(X30,X31))=k2_xboole_0(X30,X31), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 44.98/45.29  fof(c_0_9, plain, ![X28, X29]:k1_enumset1(X28,X28,X29)=k2_tarski(X28,X29), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 44.98/45.29  fof(c_0_10, plain, ![X24, X25]:r1_tarski(X24,k2_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 44.98/45.29  cnf(c_0_11, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 44.98/45.29  cnf(c_0_12, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 44.98/45.29  fof(c_0_13, plain, ![X15, X16, X17]:(~r1_tarski(X15,X16)|~r1_tarski(X16,X17)|r1_tarski(X15,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 44.98/45.29  cnf(c_0_14, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 44.98/45.29  cnf(c_0_15, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 44.98/45.29  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))))), inference(assume_negation,[status(cth)],[t143_zfmisc_1])).
% 44.98/45.29  cnf(c_0_17, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 44.98/45.29  cnf(c_0_18, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 44.98/45.29  fof(c_0_19, negated_conjecture, ((r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))&r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)))&~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 44.98/45.29  fof(c_0_20, plain, ![X32, X33, X34]:(k2_zfmisc_1(k2_xboole_0(X32,X33),X34)=k2_xboole_0(k2_zfmisc_1(X32,X34),k2_zfmisc_1(X33,X34))&k2_zfmisc_1(X34,k2_xboole_0(X32,X33))=k2_xboole_0(k2_zfmisc_1(X34,X32),k2_zfmisc_1(X34,X33))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 44.98/45.29  fof(c_0_21, plain, ![X11, X12, X13, X14]:(~r1_tarski(X11,X12)|~r1_tarski(X13,X14)|r1_tarski(k2_xboole_0(X11,X13),k2_xboole_0(X12,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_xboole_1])])).
% 44.98/45.29  cnf(c_0_22, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 44.98/45.29  cnf(c_0_23, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 44.98/45.29  cnf(c_0_24, plain, (k2_zfmisc_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 44.98/45.29  cnf(c_0_25, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 44.98/45.29  fof(c_0_26, plain, ![X26, X27]:k2_tarski(X26,X27)=k2_tarski(X27,X26), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 44.98/45.29  cnf(c_0_27, plain, (r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 44.98/45.29  cnf(c_0_28, negated_conjecture, (r1_tarski(esk2_0,k3_tarski(k1_enumset1(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk5_0,esk6_0),X1)))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 44.98/45.29  cnf(c_0_29, plain, (k2_zfmisc_1(X1,k3_tarski(k1_enumset1(X2,X2,X3)))=k3_tarski(k1_enumset1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_15]), c_0_15])).
% 44.98/45.29  cnf(c_0_30, negated_conjecture, (r1_tarski(esk1_0,k3_tarski(k1_enumset1(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),X1)))), inference(spm,[status(thm)],[c_0_22, c_0_25])).
% 44.98/45.29  cnf(c_0_31, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 44.98/45.29  cnf(c_0_32, plain, (r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),k3_tarski(k1_enumset1(X2,X2,X4)))|~r1_tarski(X3,X4)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_15]), c_0_15])).
% 44.98/45.29  cnf(c_0_33, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(esk6_0,esk6_0,X1))))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 44.98/45.29  cnf(c_0_34, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(esk4_0,esk4_0,X1))))), inference(spm,[status(thm)],[c_0_30, c_0_29])).
% 44.98/45.29  cnf(c_0_35, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_12]), c_0_12])).
% 44.98/45.29  cnf(c_0_36, negated_conjecture, (r1_tarski(k3_tarski(k1_enumset1(X1,X1,esk2_0)),k3_tarski(k1_enumset1(X2,X2,k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(esk6_0,esk6_0,X3))))))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 44.98/45.29  cnf(c_0_37, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(X1,X1,esk4_0))))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 44.98/45.29  cnf(c_0_38, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 44.98/45.29  cnf(c_0_39, negated_conjecture, (~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 44.98/45.29  cnf(c_0_40, negated_conjecture, (r1_tarski(k3_tarski(k1_enumset1(esk1_0,esk1_0,esk2_0)),k3_tarski(k1_enumset1(k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(X1,X1,esk4_0))),k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(X1,X1,esk4_0))),k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(esk6_0,esk6_0,X2))))))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 44.98/45.29  cnf(c_0_41, plain, (k2_zfmisc_1(k3_tarski(k1_enumset1(X1,X1,X2)),X3)=k3_tarski(k1_enumset1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_15]), c_0_15])).
% 44.98/45.29  cnf(c_0_42, negated_conjecture, (~r1_tarski(k3_tarski(k1_enumset1(esk1_0,esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k1_enumset1(esk3_0,esk3_0,esk5_0)),k3_tarski(k1_enumset1(esk4_0,esk4_0,esk6_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_15]), c_0_15]), c_0_15])).
% 44.98/45.29  cnf(c_0_43, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_35]), c_0_42]), ['proof']).
% 44.98/45.29  # SZS output end CNFRefutation
% 44.98/45.29  # Proof object total steps             : 44
% 44.98/45.29  # Proof object clause steps            : 27
% 44.98/45.29  # Proof object formula steps           : 17
% 44.98/45.29  # Proof object conjectures             : 15
% 44.98/45.29  # Proof object clause conjectures      : 12
% 44.98/45.29  # Proof object formula conjectures     : 3
% 44.98/45.29  # Proof object initial clauses used    : 11
% 44.98/45.29  # Proof object initial formulas used   : 8
% 44.98/45.29  # Proof object generating inferences   : 9
% 44.98/45.29  # Proof object simplifying inferences  : 15
% 44.98/45.29  # Training examples: 0 positive, 0 negative
% 44.98/45.29  # Parsed axioms                        : 12
% 44.98/45.29  # Removed by relevancy pruning/SinE    : 0
% 44.98/45.29  # Initial clauses                      : 15
% 44.98/45.29  # Removed in clause preprocessing      : 3
% 44.98/45.29  # Initial clauses in saturation        : 12
% 44.98/45.29  # Processed clauses                    : 29574
% 44.98/45.29  # ...of these trivial                  : 4164
% 44.98/45.29  # ...subsumed                          : 11053
% 44.98/45.29  # ...remaining for further processing  : 14357
% 44.98/45.29  # Other redundant clauses eliminated   : 0
% 44.98/45.29  # Clauses deleted for lack of memory   : 90310
% 44.98/45.29  # Backward-subsumed                    : 158
% 44.98/45.29  # Backward-rewritten                   : 439
% 44.98/45.29  # Generated clauses                    : 2608271
% 44.98/45.29  # ...of the previous two non-trivial   : 2169960
% 44.98/45.29  # Contextual simplify-reflections      : 0
% 44.98/45.29  # Paramodulations                      : 2608271
% 44.98/45.29  # Factorizations                       : 0
% 44.98/45.29  # Equation resolutions                 : 0
% 44.98/45.29  # Propositional unsat checks           : 0
% 44.98/45.29  #    Propositional check models        : 0
% 44.98/45.29  #    Propositional check unsatisfiable : 0
% 44.98/45.29  #    Propositional clauses             : 0
% 44.98/45.29  #    Propositional clauses after purity: 0
% 44.98/45.29  #    Propositional unsat core size     : 0
% 44.98/45.29  #    Propositional preprocessing time  : 0.000
% 44.98/45.29  #    Propositional encoding time       : 0.000
% 44.98/45.29  #    Propositional solver time         : 0.000
% 44.98/45.29  #    Success case prop preproc time    : 0.000
% 44.98/45.29  #    Success case prop encoding time   : 0.000
% 44.98/45.29  #    Success case prop solver time     : 0.000
% 44.98/45.29  # Current number of processed clauses  : 13748
% 44.98/45.29  #    Positive orientable unit clauses  : 8441
% 44.98/45.29  #    Positive unorientable unit clauses: 3
% 44.98/45.29  #    Negative unit clauses             : 1
% 44.98/45.29  #    Non-unit-clauses                  : 5303
% 44.98/45.29  # Current number of unprocessed clauses: 1283320
% 44.98/45.29  # ...number of literals in the above   : 1326940
% 44.98/45.29  # Current number of archived formulas  : 0
% 44.98/45.29  # Current number of archived clauses   : 612
% 44.98/45.29  # Clause-clause subsumption calls (NU) : 3760771
% 44.98/45.29  # Rec. Clause-clause subsumption calls : 3434841
% 44.98/45.29  # Non-unit clause-clause subsumptions  : 11188
% 44.98/45.29  # Unit Clause-clause subsumption calls : 44882
% 44.98/45.29  # Rewrite failures with RHS unbound    : 3782
% 44.98/45.29  # BW rewrite match attempts            : 3515192
% 44.98/45.29  # BW rewrite match successes           : 407
% 44.98/45.29  # Condensation attempts                : 0
% 44.98/45.29  # Condensation successes               : 0
% 44.98/45.29  # Termbank termtop insertions          : 142974297
% 45.09/45.37  
% 45.09/45.37  # -------------------------------------------------
% 45.09/45.37  # User time                : 43.767 s
% 45.09/45.37  # System time              : 1.190 s
% 45.09/45.37  # Total time               : 44.956 s
% 45.09/45.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
