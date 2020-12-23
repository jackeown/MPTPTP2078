%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:27 EST 2020

% Result     : Theorem 15.22s
% Output     : CNFRefutation 15.22s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 221 expanded)
%              Number of clauses        :   31 (  94 expanded)
%              Number of leaves         :   10 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :   83 ( 300 expanded)
%              Number of equality atoms :   17 ( 148 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t118_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t143_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
        & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
     => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(c_0_10,plain,(
    ! [X26,X27] : k3_tarski(k2_tarski(X26,X27)) = k2_xboole_0(X26,X27) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X17,X18] : k1_enumset1(X17,X17,X18) = k2_tarski(X17,X18) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X10,X11] : r1_tarski(X10,k2_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_13,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X19,X20,X21] : k2_enumset1(X19,X19,X20,X21) = k1_enumset1(X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_16,plain,(
    ! [X22,X23,X24,X25] : k3_enumset1(X22,X22,X23,X24,X25) = k2_enumset1(X22,X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_17,plain,(
    ! [X28,X29,X30] :
      ( ( r1_tarski(k2_zfmisc_1(X28,X30),k2_zfmisc_1(X29,X30))
        | ~ r1_tarski(X28,X29) )
      & ( r1_tarski(k2_zfmisc_1(X30,X28),k2_zfmisc_1(X30,X29))
        | ~ r1_tarski(X28,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X15,X16] : k2_tarski(X15,X16) = k2_tarski(X16,X15) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_23,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X8,X9)
      | r1_tarski(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_24,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
          & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
       => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    inference(assume_negation,[status(cth)],[t143_zfmisc_1])).

cnf(c_0_27,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_31,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))
    & r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))
    & ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

cnf(c_0_32,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_tarski(k3_enumset1(X1,X1,X1,X1,X3)),X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_25])).

cnf(c_0_33,plain,
    ( k3_enumset1(X1,X1,X1,X1,X2) = k3_enumset1(X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_14]),c_0_14]),c_0_20]),c_0_20]),c_0_21]),c_0_21])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,k3_tarski(k3_enumset1(X3,X3,X3,X3,X4))))
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_36,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | ~ r1_tarski(X14,X13)
      | r1_tarski(k2_xboole_0(X12,X14),X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_37,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_tarski(k3_enumset1(X3,X3,X3,X3,X1)),X2)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)),X4))
    | ~ r1_tarski(X1,k2_zfmisc_1(X3,X4)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k3_enumset1(X1,X1,X1,X1,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_33])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)),X4))
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( r1_tarski(k3_tarski(k3_enumset1(X1,X1,X1,X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(k3_tarski(k3_enumset1(X1,X1,X1,X1,esk5_0)),k3_tarski(k3_enumset1(X2,X2,X2,X2,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1)),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k3_tarski(k3_enumset1(X1,X1,X1,X1,esk2_0)),k2_zfmisc_1(k3_tarski(k3_enumset1(X2,X2,X2,X2,esk5_0)),k3_tarski(k3_enumset1(X3,X3,X3,X3,esk6_0))))
    | ~ r1_tarski(X1,k2_zfmisc_1(k3_tarski(k3_enumset1(X2,X2,X2,X2,esk5_0)),k3_tarski(k3_enumset1(X3,X3,X3,X3,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1)),k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,X2)))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)),k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_19]),c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_20]),c_0_21]),c_0_21]),c_0_21])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:59:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 15.22/15.42  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S081N
% 15.22/15.42  # and selection function SelectCQArNTNp.
% 15.22/15.42  #
% 15.22/15.42  # Preprocessing time       : 0.027 s
% 15.22/15.42  # Presaturation interreduction done
% 15.22/15.42  
% 15.22/15.42  # Proof found!
% 15.22/15.42  # SZS status Theorem
% 15.22/15.42  # SZS output start CNFRefutation
% 15.22/15.42  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 15.22/15.42  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 15.22/15.42  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 15.22/15.42  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 15.22/15.42  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 15.22/15.42  fof(t118_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>(r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 15.22/15.42  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 15.22/15.42  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 15.22/15.42  fof(t143_zfmisc_1, conjecture, ![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 15.22/15.42  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 15.22/15.42  fof(c_0_10, plain, ![X26, X27]:k3_tarski(k2_tarski(X26,X27))=k2_xboole_0(X26,X27), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 15.22/15.42  fof(c_0_11, plain, ![X17, X18]:k1_enumset1(X17,X17,X18)=k2_tarski(X17,X18), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 15.22/15.42  fof(c_0_12, plain, ![X10, X11]:r1_tarski(X10,k2_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 15.22/15.42  cnf(c_0_13, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 15.22/15.42  cnf(c_0_14, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 15.22/15.42  fof(c_0_15, plain, ![X19, X20, X21]:k2_enumset1(X19,X19,X20,X21)=k1_enumset1(X19,X20,X21), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 15.22/15.42  fof(c_0_16, plain, ![X22, X23, X24, X25]:k3_enumset1(X22,X22,X23,X24,X25)=k2_enumset1(X22,X23,X24,X25), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 15.22/15.42  fof(c_0_17, plain, ![X28, X29, X30]:((r1_tarski(k2_zfmisc_1(X28,X30),k2_zfmisc_1(X29,X30))|~r1_tarski(X28,X29))&(r1_tarski(k2_zfmisc_1(X30,X28),k2_zfmisc_1(X30,X29))|~r1_tarski(X28,X29))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).
% 15.22/15.42  cnf(c_0_18, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 15.22/15.42  cnf(c_0_19, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 15.22/15.42  cnf(c_0_20, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 15.22/15.42  cnf(c_0_21, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 15.22/15.42  fof(c_0_22, plain, ![X15, X16]:k2_tarski(X15,X16)=k2_tarski(X16,X15), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 15.22/15.42  fof(c_0_23, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|~r1_tarski(X8,X9)|r1_tarski(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 15.22/15.42  cnf(c_0_24, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 15.22/15.42  cnf(c_0_25, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21])).
% 15.22/15.42  fof(c_0_26, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))))), inference(assume_negation,[status(cth)],[t143_zfmisc_1])).
% 15.22/15.42  cnf(c_0_27, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 15.22/15.42  cnf(c_0_28, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 15.22/15.42  cnf(c_0_29, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 15.22/15.42  cnf(c_0_30, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3))))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 15.22/15.42  fof(c_0_31, negated_conjecture, ((r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))&r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)))&~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 15.22/15.42  cnf(c_0_32, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_tarski(k3_enumset1(X1,X1,X1,X1,X3)),X2))), inference(spm,[status(thm)],[c_0_27, c_0_25])).
% 15.22/15.42  cnf(c_0_33, plain, (k3_enumset1(X1,X1,X1,X1,X2)=k3_enumset1(X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_14]), c_0_14]), c_0_20]), c_0_20]), c_0_21]), c_0_21])).
% 15.22/15.42  cnf(c_0_34, plain, (r1_tarski(X1,k2_zfmisc_1(X2,k3_tarski(k3_enumset1(X3,X3,X3,X3,X4))))|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 15.22/15.42  cnf(c_0_35, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 15.22/15.42  fof(c_0_36, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|~r1_tarski(X14,X13)|r1_tarski(k2_xboole_0(X12,X14),X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 15.22/15.42  cnf(c_0_37, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_tarski(k3_enumset1(X3,X3,X3,X3,X1)),X2))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 15.22/15.42  cnf(c_0_38, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,X1))))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 15.22/15.42  cnf(c_0_39, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 15.22/15.42  cnf(c_0_40, plain, (r1_tarski(X1,k2_zfmisc_1(k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)),X4))|~r1_tarski(X1,k2_zfmisc_1(X3,X4))), inference(spm,[status(thm)],[c_0_29, c_0_37])).
% 15.22/15.42  cnf(c_0_41, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k3_enumset1(X1,X1,X1,X1,esk6_0))))), inference(spm,[status(thm)],[c_0_38, c_0_33])).
% 15.22/15.42  cnf(c_0_42, plain, (r1_tarski(X1,k2_zfmisc_1(k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)),X4))|~r1_tarski(X1,k2_zfmisc_1(X2,X4))), inference(spm,[status(thm)],[c_0_29, c_0_32])).
% 15.22/15.42  cnf(c_0_43, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 15.22/15.42  cnf(c_0_44, plain, (r1_tarski(k3_tarski(k3_enumset1(X1,X1,X1,X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_19]), c_0_20]), c_0_21])).
% 15.22/15.42  cnf(c_0_45, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(k3_tarski(k3_enumset1(X1,X1,X1,X1,esk5_0)),k3_tarski(k3_enumset1(X2,X2,X2,X2,esk6_0))))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 15.22/15.42  cnf(c_0_46, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1)),esk4_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 15.22/15.42  cnf(c_0_47, negated_conjecture, (~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 15.22/15.42  cnf(c_0_48, negated_conjecture, (r1_tarski(k3_tarski(k3_enumset1(X1,X1,X1,X1,esk2_0)),k2_zfmisc_1(k3_tarski(k3_enumset1(X2,X2,X2,X2,esk5_0)),k3_tarski(k3_enumset1(X3,X3,X3,X3,esk6_0))))|~r1_tarski(X1,k2_zfmisc_1(k3_tarski(k3_enumset1(X2,X2,X2,X2,esk5_0)),k3_tarski(k3_enumset1(X3,X3,X3,X3,esk6_0))))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 15.22/15.42  cnf(c_0_49, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1)),k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,X2))))), inference(spm,[status(thm)],[c_0_34, c_0_46])).
% 15.22/15.42  cnf(c_0_50, negated_conjecture, (~r1_tarski(k3_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)),k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_19]), c_0_19]), c_0_19]), c_0_20]), c_0_20]), c_0_20]), c_0_21]), c_0_21]), c_0_21])).
% 15.22/15.42  cnf(c_0_51, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), ['proof']).
% 15.22/15.42  # SZS output end CNFRefutation
% 15.22/15.42  # Proof object total steps             : 52
% 15.22/15.42  # Proof object clause steps            : 31
% 15.22/15.42  # Proof object formula steps           : 21
% 15.22/15.42  # Proof object conjectures             : 14
% 15.22/15.42  # Proof object clause conjectures      : 11
% 15.22/15.42  # Proof object formula conjectures     : 3
% 15.22/15.42  # Proof object initial clauses used    : 13
% 15.22/15.42  # Proof object initial formulas used   : 10
% 15.22/15.42  # Proof object generating inferences   : 13
% 15.22/15.42  # Proof object simplifying inferences  : 23
% 15.22/15.42  # Training examples: 0 positive, 0 negative
% 15.22/15.42  # Parsed axioms                        : 10
% 15.22/15.42  # Removed by relevancy pruning/SinE    : 0
% 15.22/15.42  # Initial clauses                      : 13
% 15.22/15.42  # Removed in clause preprocessing      : 4
% 15.22/15.42  # Initial clauses in saturation        : 9
% 15.22/15.42  # Processed clauses                    : 22184
% 15.22/15.42  # ...of these trivial                  : 8866
% 15.22/15.42  # ...subsumed                          : 2921
% 15.22/15.42  # ...remaining for further processing  : 10397
% 15.22/15.42  # Other redundant clauses eliminated   : 0
% 15.22/15.42  # Clauses deleted for lack of memory   : 0
% 15.22/15.42  # Backward-subsumed                    : 166
% 15.22/15.42  # Backward-rewritten                   : 214
% 15.22/15.42  # Generated clauses                    : 1139631
% 15.22/15.42  # ...of the previous two non-trivial   : 1079087
% 15.22/15.42  # Contextual simplify-reflections      : 0
% 15.22/15.42  # Paramodulations                      : 1139631
% 15.22/15.42  # Factorizations                       : 0
% 15.22/15.42  # Equation resolutions                 : 0
% 15.22/15.42  # Propositional unsat checks           : 0
% 15.22/15.42  #    Propositional check models        : 0
% 15.22/15.42  #    Propositional check unsatisfiable : 0
% 15.22/15.42  #    Propositional clauses             : 0
% 15.22/15.42  #    Propositional clauses after purity: 0
% 15.22/15.42  #    Propositional unsat core size     : 0
% 15.22/15.42  #    Propositional preprocessing time  : 0.000
% 15.22/15.42  #    Propositional encoding time       : 0.000
% 15.22/15.42  #    Propositional solver time         : 0.000
% 15.22/15.42  #    Success case prop preproc time    : 0.000
% 15.22/15.42  #    Success case prop encoding time   : 0.000
% 15.22/15.42  #    Success case prop solver time     : 0.000
% 15.22/15.42  # Current number of processed clauses  : 10008
% 15.22/15.42  #    Positive orientable unit clauses  : 5948
% 15.22/15.42  #    Positive unorientable unit clauses: 1
% 15.22/15.42  #    Negative unit clauses             : 1
% 15.22/15.42  #    Non-unit-clauses                  : 4058
% 15.22/15.42  # Current number of unprocessed clauses: 1056609
% 15.22/15.42  # ...number of literals in the above   : 1064831
% 15.22/15.42  # Current number of archived formulas  : 0
% 15.22/15.42  # Current number of archived clauses   : 393
% 15.22/15.42  # Clause-clause subsumption calls (NU) : 3372159
% 15.22/15.42  # Rec. Clause-clause subsumption calls : 3256613
% 15.22/15.42  # Non-unit clause-clause subsumptions  : 3087
% 15.22/15.42  # Unit Clause-clause subsumption calls : 29157
% 15.22/15.42  # Rewrite failures with RHS unbound    : 0
% 15.22/15.42  # BW rewrite match attempts            : 1621167
% 15.22/15.42  # BW rewrite match successes           : 230
% 15.22/15.42  # Condensation attempts                : 0
% 15.22/15.42  # Condensation successes               : 0
% 15.22/15.42  # Termbank termtop insertions          : 53602664
% 15.23/15.48  
% 15.23/15.48  # -------------------------------------------------
% 15.23/15.48  # User time                : 14.609 s
% 15.23/15.48  # System time              : 0.511 s
% 15.23/15.48  # Total time               : 15.120 s
% 15.23/15.48  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
