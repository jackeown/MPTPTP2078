%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:27 EST 2020

% Result     : Theorem 7.61s
% Output     : CNFRefutation 7.61s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 346 expanded)
%              Number of clauses        :   39 ( 163 expanded)
%              Number of leaves         :   10 (  90 expanded)
%              Depth                    :   13
%              Number of atoms          :   95 ( 413 expanded)
%              Number of equality atoms :   32 ( 291 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t9_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t13_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

fof(c_0_10,plain,(
    ! [X24,X25] : k3_tarski(k2_tarski(X24,X25)) = k2_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X22,X23] : k1_enumset1(X22,X22,X23) = k2_tarski(X22,X23) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_tarski(X19,X20)
      | r1_tarski(k2_xboole_0(X19,X21),k2_xboole_0(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_xboole_1])])).

cnf(c_0_13,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
          & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
       => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    inference(assume_negation,[status(cth)],[t143_zfmisc_1])).

cnf(c_0_16,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_18,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))
    & r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))
    & ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_19,plain,(
    ! [X26,X27,X28] :
      ( k2_zfmisc_1(k2_xboole_0(X26,X27),X28) = k2_xboole_0(k2_zfmisc_1(X26,X28),k2_zfmisc_1(X27,X28))
      & k2_zfmisc_1(X28,k2_xboole_0(X26,X27)) = k2_xboole_0(k2_zfmisc_1(X28,X26),k2_zfmisc_1(X28,X27)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

fof(c_0_20,plain,(
    ! [X11,X12] :
      ( ~ r1_tarski(X11,X12)
      | k2_xboole_0(X11,X12) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_21,plain,(
    ! [X17,X18] : r1_tarski(X17,k2_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_22,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),k3_tarski(k1_enumset1(X2,X2,X3)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_27,plain,(
    ! [X7,X8] : k2_xboole_0(X7,X8) = k2_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k3_tarski(k1_enumset1(esk2_0,esk2_0,X1)),k3_tarski(k1_enumset1(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk5_0,esk6_0),X1))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(X1,k3_tarski(k1_enumset1(X2,X2,X3))) = k3_tarski(k1_enumset1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_17]),c_0_17])).

cnf(c_0_30,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_17])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_17])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_33,plain,(
    ! [X9,X10] :
      ( ( r1_tarski(X9,X10)
        | X9 != X10 )
      & ( r1_tarski(X10,X9)
        | X9 != X10 )
      & ( ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X10,X9)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k3_tarski(k1_enumset1(esk2_0,esk2_0,k2_zfmisc_1(esk5_0,X1))),k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(esk6_0,esk6_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( k3_tarski(k1_enumset1(X1,X1,k3_tarski(k1_enumset1(X1,X1,X2)))) = k3_tarski(k1_enumset1(X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k3_tarski(k1_enumset1(X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_17]),c_0_17])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_38,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k3_tarski(k1_enumset1(esk2_0,esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(esk6_0,esk6_0,X1))))),k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(esk6_0,esk6_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(k3_tarski(k1_enumset1(esk1_0,esk1_0,X1)),k3_tarski(k1_enumset1(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),X1))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_37])).

fof(c_0_42,plain,(
    ! [X13,X14,X15,X16] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X15,X16)
      | r1_tarski(k2_xboole_0(X13,X15),k2_xboole_0(X14,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_xboole_1])])).

cnf(c_0_43,negated_conjecture,
    ( k3_tarski(k1_enumset1(esk2_0,esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(esk6_0,esk6_0,X1))))) = k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(esk6_0,esk6_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k3_tarski(k1_enumset1(esk1_0,esk1_0,k2_zfmisc_1(esk3_0,X1))),k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(esk4_0,esk4_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_29])).

cnf(c_0_45,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(esk6_0,esk6_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k3_tarski(k1_enumset1(esk1_0,esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(esk4_0,esk4_0,X1))))),k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(esk4_0,esk4_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_35])).

cnf(c_0_48,plain,
    ( k3_tarski(k1_enumset1(X1,X1,k3_tarski(k1_enumset1(X2,X2,X1)))) = k3_tarski(k1_enumset1(X2,X2,X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_40])).

cnf(c_0_49,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),k3_tarski(k1_enumset1(X2,X2,X4)))
    | ~ r1_tarski(X3,X4)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_17]),c_0_17])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(X1,X1,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_36])).

cnf(c_0_51,negated_conjecture,
    ( k3_tarski(k1_enumset1(esk1_0,esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(esk4_0,esk4_0,X1))))) = k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(esk4_0,esk4_0,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_47]),c_0_36]),c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k3_tarski(k1_enumset1(X1,X1,esk2_0)),k3_tarski(k1_enumset1(X2,X2,k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(X3,X3,esk6_0))))))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(esk4_0,esk4_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_51])).

cnf(c_0_54,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_55,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k3_tarski(k1_enumset1(esk1_0,esk1_0,esk2_0)),k3_tarski(k1_enumset1(k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(esk4_0,esk4_0,X1))),k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(esk4_0,esk4_0,X1))),k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(X2,X2,esk6_0)))))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,plain,
    ( k2_zfmisc_1(k3_tarski(k1_enumset1(X1,X1,X2)),X3) = k3_tarski(k1_enumset1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_17]),c_0_17])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k1_enumset1(esk1_0,esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k1_enumset1(esk3_0,esk3_0,esk5_0)),k3_tarski(k1_enumset1(esk4_0,esk4_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_17]),c_0_17]),c_0_17])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:04:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 7.61/7.79  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S081N
% 7.61/7.79  # and selection function SelectCQArNTNp.
% 7.61/7.79  #
% 7.61/7.79  # Preprocessing time       : 0.027 s
% 7.61/7.79  # Presaturation interreduction done
% 7.61/7.79  
% 7.61/7.79  # Proof found!
% 7.61/7.79  # SZS status Theorem
% 7.61/7.79  # SZS output start CNFRefutation
% 7.61/7.79  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 7.61/7.79  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 7.61/7.79  fof(t9_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_xboole_1)).
% 7.61/7.79  fof(t143_zfmisc_1, conjecture, ![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 7.61/7.79  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 7.61/7.79  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.61/7.79  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.61/7.79  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 7.61/7.79  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.61/7.79  fof(t13_xboole_1, axiom, ![X1, X2, X3, X4]:((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_xboole_1)).
% 7.61/7.79  fof(c_0_10, plain, ![X24, X25]:k3_tarski(k2_tarski(X24,X25))=k2_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 7.61/7.79  fof(c_0_11, plain, ![X22, X23]:k1_enumset1(X22,X22,X23)=k2_tarski(X22,X23), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 7.61/7.79  fof(c_0_12, plain, ![X19, X20, X21]:(~r1_tarski(X19,X20)|r1_tarski(k2_xboole_0(X19,X21),k2_xboole_0(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_xboole_1])])).
% 7.61/7.79  cnf(c_0_13, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 7.61/7.79  cnf(c_0_14, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 7.61/7.79  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))))), inference(assume_negation,[status(cth)],[t143_zfmisc_1])).
% 7.61/7.79  cnf(c_0_16, plain, (r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 7.61/7.79  cnf(c_0_17, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 7.61/7.79  fof(c_0_18, negated_conjecture, ((r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))&r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)))&~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 7.61/7.79  fof(c_0_19, plain, ![X26, X27, X28]:(k2_zfmisc_1(k2_xboole_0(X26,X27),X28)=k2_xboole_0(k2_zfmisc_1(X26,X28),k2_zfmisc_1(X27,X28))&k2_zfmisc_1(X28,k2_xboole_0(X26,X27))=k2_xboole_0(k2_zfmisc_1(X28,X26),k2_zfmisc_1(X28,X27))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 7.61/7.79  fof(c_0_20, plain, ![X11, X12]:(~r1_tarski(X11,X12)|k2_xboole_0(X11,X12)=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 7.61/7.79  fof(c_0_21, plain, ![X17, X18]:r1_tarski(X17,k2_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 7.61/7.79  cnf(c_0_22, plain, (r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),k3_tarski(k1_enumset1(X2,X2,X3)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_17])).
% 7.61/7.79  cnf(c_0_23, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 7.61/7.79  cnf(c_0_24, plain, (k2_zfmisc_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 7.61/7.79  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 7.61/7.79  cnf(c_0_26, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 7.61/7.79  fof(c_0_27, plain, ![X7, X8]:k2_xboole_0(X7,X8)=k2_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 7.61/7.79  cnf(c_0_28, negated_conjecture, (r1_tarski(k3_tarski(k1_enumset1(esk2_0,esk2_0,X1)),k3_tarski(k1_enumset1(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk5_0,esk6_0),X1)))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 7.61/7.79  cnf(c_0_29, plain, (k2_zfmisc_1(X1,k3_tarski(k1_enumset1(X2,X2,X3)))=k3_tarski(k1_enumset1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_17]), c_0_17])).
% 7.61/7.79  cnf(c_0_30, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_17])).
% 7.61/7.79  cnf(c_0_31, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_26, c_0_17])).
% 7.61/7.79  cnf(c_0_32, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 7.61/7.79  fof(c_0_33, plain, ![X9, X10]:(((r1_tarski(X9,X10)|X9!=X10)&(r1_tarski(X10,X9)|X9!=X10))&(~r1_tarski(X9,X10)|~r1_tarski(X10,X9)|X9=X10)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 7.61/7.79  cnf(c_0_34, negated_conjecture, (r1_tarski(k3_tarski(k1_enumset1(esk2_0,esk2_0,k2_zfmisc_1(esk5_0,X1))),k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(esk6_0,esk6_0,X1))))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 7.61/7.79  cnf(c_0_35, plain, (k3_tarski(k1_enumset1(X1,X1,k3_tarski(k1_enumset1(X1,X1,X2))))=k3_tarski(k1_enumset1(X1,X1,X2))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 7.61/7.79  cnf(c_0_36, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k3_tarski(k1_enumset1(X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_17]), c_0_17])).
% 7.61/7.79  cnf(c_0_37, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 7.61/7.79  cnf(c_0_38, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 7.61/7.79  cnf(c_0_39, negated_conjecture, (r1_tarski(k3_tarski(k1_enumset1(esk2_0,esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(esk6_0,esk6_0,X1))))),k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(esk6_0,esk6_0,X1))))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 7.61/7.79  cnf(c_0_40, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X1)))), inference(spm,[status(thm)],[c_0_31, c_0_36])).
% 7.61/7.79  cnf(c_0_41, negated_conjecture, (r1_tarski(k3_tarski(k1_enumset1(esk1_0,esk1_0,X1)),k3_tarski(k1_enumset1(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),X1)))), inference(spm,[status(thm)],[c_0_22, c_0_37])).
% 7.61/7.79  fof(c_0_42, plain, ![X13, X14, X15, X16]:(~r1_tarski(X13,X14)|~r1_tarski(X15,X16)|r1_tarski(k2_xboole_0(X13,X15),k2_xboole_0(X14,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_xboole_1])])).
% 7.61/7.79  cnf(c_0_43, negated_conjecture, (k3_tarski(k1_enumset1(esk2_0,esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(esk6_0,esk6_0,X1)))))=k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(esk6_0,esk6_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 7.61/7.79  cnf(c_0_44, negated_conjecture, (r1_tarski(k3_tarski(k1_enumset1(esk1_0,esk1_0,k2_zfmisc_1(esk3_0,X1))),k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(esk4_0,esk4_0,X1))))), inference(spm,[status(thm)],[c_0_41, c_0_29])).
% 7.61/7.79  cnf(c_0_45, plain, (r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 7.61/7.79  cnf(c_0_46, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(esk6_0,esk6_0,X1))))), inference(spm,[status(thm)],[c_0_31, c_0_43])).
% 7.61/7.79  cnf(c_0_47, negated_conjecture, (r1_tarski(k3_tarski(k1_enumset1(esk1_0,esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(esk4_0,esk4_0,X1))))),k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(esk4_0,esk4_0,X1))))), inference(spm,[status(thm)],[c_0_44, c_0_35])).
% 7.61/7.79  cnf(c_0_48, plain, (k3_tarski(k1_enumset1(X1,X1,k3_tarski(k1_enumset1(X2,X2,X1))))=k3_tarski(k1_enumset1(X2,X2,X1))), inference(spm,[status(thm)],[c_0_30, c_0_40])).
% 7.61/7.79  cnf(c_0_49, plain, (r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),k3_tarski(k1_enumset1(X2,X2,X4)))|~r1_tarski(X3,X4)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_17]), c_0_17])).
% 7.61/7.79  cnf(c_0_50, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(X1,X1,esk6_0))))), inference(spm,[status(thm)],[c_0_46, c_0_36])).
% 7.61/7.79  cnf(c_0_51, negated_conjecture, (k3_tarski(k1_enumset1(esk1_0,esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(esk4_0,esk4_0,X1)))))=k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(esk4_0,esk4_0,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_47]), c_0_36]), c_0_48])).
% 7.61/7.79  cnf(c_0_52, negated_conjecture, (r1_tarski(k3_tarski(k1_enumset1(X1,X1,esk2_0)),k3_tarski(k1_enumset1(X2,X2,k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(X3,X3,esk6_0))))))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 7.61/7.79  cnf(c_0_53, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(esk4_0,esk4_0,X1))))), inference(spm,[status(thm)],[c_0_31, c_0_51])).
% 7.61/7.79  cnf(c_0_54, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 7.61/7.79  cnf(c_0_55, negated_conjecture, (~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 7.61/7.79  cnf(c_0_56, negated_conjecture, (r1_tarski(k3_tarski(k1_enumset1(esk1_0,esk1_0,esk2_0)),k3_tarski(k1_enumset1(k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(esk4_0,esk4_0,X1))),k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(esk4_0,esk4_0,X1))),k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(X2,X2,esk6_0))))))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 7.61/7.79  cnf(c_0_57, plain, (k2_zfmisc_1(k3_tarski(k1_enumset1(X1,X1,X2)),X3)=k3_tarski(k1_enumset1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_17]), c_0_17])).
% 7.61/7.79  cnf(c_0_58, negated_conjecture, (~r1_tarski(k3_tarski(k1_enumset1(esk1_0,esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k1_enumset1(esk3_0,esk3_0,esk5_0)),k3_tarski(k1_enumset1(esk4_0,esk4_0,esk6_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_17]), c_0_17]), c_0_17])).
% 7.61/7.79  cnf(c_0_59, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), ['proof']).
% 7.61/7.79  # SZS output end CNFRefutation
% 7.61/7.79  # Proof object total steps             : 60
% 7.61/7.79  # Proof object clause steps            : 39
% 7.61/7.79  # Proof object formula steps           : 21
% 7.61/7.79  # Proof object conjectures             : 21
% 7.61/7.79  # Proof object clause conjectures      : 18
% 7.61/7.79  # Proof object formula conjectures     : 3
% 7.61/7.79  # Proof object initial clauses used    : 13
% 7.61/7.79  # Proof object initial formulas used   : 10
% 7.61/7.79  # Proof object generating inferences   : 17
% 7.61/7.79  # Proof object simplifying inferences  : 21
% 7.61/7.79  # Training examples: 0 positive, 0 negative
% 7.61/7.79  # Parsed axioms                        : 10
% 7.61/7.79  # Removed by relevancy pruning/SinE    : 0
% 7.61/7.79  # Initial clauses                      : 15
% 7.61/7.79  # Removed in clause preprocessing      : 2
% 7.61/7.79  # Initial clauses in saturation        : 13
% 7.61/7.79  # Processed clauses                    : 6485
% 7.61/7.79  # ...of these trivial                  : 1311
% 7.61/7.79  # ...subsumed                          : 2196
% 7.61/7.79  # ...remaining for further processing  : 2978
% 7.61/7.79  # Other redundant clauses eliminated   : 2
% 7.61/7.79  # Clauses deleted for lack of memory   : 0
% 7.61/7.79  # Backward-subsumed                    : 6
% 7.61/7.79  # Backward-rewritten                   : 147
% 7.61/7.79  # Generated clauses                    : 549141
% 7.61/7.79  # ...of the previous two non-trivial   : 509395
% 7.61/7.79  # Contextual simplify-reflections      : 0
% 7.61/7.79  # Paramodulations                      : 549139
% 7.61/7.79  # Factorizations                       : 0
% 7.61/7.79  # Equation resolutions                 : 2
% 7.61/7.79  # Propositional unsat checks           : 0
% 7.61/7.79  #    Propositional check models        : 0
% 7.61/7.79  #    Propositional check unsatisfiable : 0
% 7.61/7.79  #    Propositional clauses             : 0
% 7.61/7.79  #    Propositional clauses after purity: 0
% 7.61/7.79  #    Propositional unsat core size     : 0
% 7.61/7.79  #    Propositional preprocessing time  : 0.000
% 7.61/7.79  #    Propositional encoding time       : 0.000
% 7.61/7.79  #    Propositional solver time         : 0.000
% 7.61/7.79  #    Success case prop preproc time    : 0.000
% 7.61/7.79  #    Success case prop encoding time   : 0.000
% 7.61/7.79  #    Success case prop solver time     : 0.000
% 7.61/7.79  # Current number of processed clauses  : 2811
% 7.61/7.79  #    Positive orientable unit clauses  : 2104
% 7.61/7.79  #    Positive unorientable unit clauses: 1
% 7.61/7.79  #    Negative unit clauses             : 1
% 7.61/7.79  #    Non-unit-clauses                  : 705
% 7.61/7.79  # Current number of unprocessed clauses: 502346
% 7.61/7.79  # ...number of literals in the above   : 509799
% 7.61/7.79  # Current number of archived formulas  : 0
% 7.61/7.79  # Current number of archived clauses   : 167
% 7.61/7.79  # Clause-clause subsumption calls (NU) : 104888
% 7.61/7.79  # Rec. Clause-clause subsumption calls : 104522
% 7.61/7.79  # Non-unit clause-clause subsumptions  : 2177
% 7.61/7.79  # Unit Clause-clause subsumption calls : 8994
% 7.61/7.79  # Rewrite failures with RHS unbound    : 0
% 7.61/7.79  # BW rewrite match attempts            : 482561
% 7.61/7.79  # BW rewrite match successes           : 77
% 7.61/7.79  # Condensation attempts                : 0
% 7.61/7.79  # Condensation successes               : 0
% 7.61/7.79  # Termbank termtop insertions          : 32115814
% 7.61/7.82  
% 7.61/7.82  # -------------------------------------------------
% 7.61/7.82  # User time                : 7.150 s
% 7.61/7.82  # System time              : 0.340 s
% 7.61/7.82  # Total time               : 7.491 s
% 7.61/7.82  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
