%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:10 EST 2020

% Result     : Theorem 35.16s
% Output     : CNFRefutation 35.16s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 333 expanded)
%              Number of clauses        :   35 ( 150 expanded)
%              Number of leaves         :   12 (  91 expanded)
%              Depth                    :   12
%              Number of atoms          :   91 ( 422 expanded)
%              Number of equality atoms :   25 ( 262 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t109_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t79_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(t110_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k5_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

fof(t81_zfmisc_1,conjecture,(
    ! [X1,X2] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)),k1_zfmisc_1(k2_xboole_0(X1,X2))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_zfmisc_1)).

fof(c_0_12,plain,(
    ! [X29,X30] : k3_tarski(k2_tarski(X29,X30)) = k2_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X20,X21] : k1_enumset1(X20,X20,X21) = k2_tarski(X20,X21) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X16,X17] : r1_tarski(X16,k2_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_15,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X22,X23,X24] : k2_enumset1(X22,X22,X23,X24) = k1_enumset1(X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_18,plain,(
    ! [X25,X26,X27,X28] : k3_enumset1(X25,X25,X26,X27,X28) = k2_enumset1(X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_19,plain,(
    ! [X18,X19] : k2_xboole_0(X18,X19) = k5_xboole_0(X18,k4_xboole_0(X19,X18)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,X11)
      | r1_tarski(X10,k2_xboole_0(X12,X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

fof(c_0_26,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | r1_tarski(k4_xboole_0(X7,X9),X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_xboole_1])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_28,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_30,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_31,plain,(
    ! [X31,X32] :
      ( ~ r1_tarski(X31,X32)
      | r1_tarski(k1_zfmisc_1(X31),k1_zfmisc_1(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).

fof(c_0_32,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X15,X14)
      | r1_tarski(k5_xboole_0(X13,X15),X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t110_xboole_1])])).

cnf(c_0_33,plain,
    ( r1_tarski(k4_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( r1_tarski(k5_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,k4_xboole_0(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))
    | ~ r1_tarski(X1,X3) ),
    inference(rw,[status(thm)],[c_0_35,c_0_28])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_36])).

fof(c_0_42,negated_conjecture,(
    ~ ! [X1,X2] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)),k1_zfmisc_1(k2_xboole_0(X1,X2))) ),
    inference(assume_negation,[status(cth)],[t81_zfmisc_1])).

cnf(c_0_43,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(k5_xboole_0(X1,k4_xboole_0(X2,X1)))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_34])).

cnf(c_0_44,plain,
    ( r1_tarski(k5_xboole_0(X1,k4_xboole_0(X2,X3)),k5_xboole_0(X2,k4_xboole_0(X4,X2)))
    | ~ r1_tarski(X1,k5_xboole_0(X2,k4_xboole_0(X4,X2))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_46,negated_conjecture,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0)),k1_zfmisc_1(k2_xboole_0(esk1_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])).

cnf(c_0_47,plain,
    ( r1_tarski(k4_xboole_0(k1_zfmisc_1(X1),X2),k1_zfmisc_1(k5_xboole_0(X1,k4_xboole_0(X3,X1)))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_43])).

cnf(c_0_48,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_49,plain,
    ( r1_tarski(k5_xboole_0(X1,k4_xboole_0(X2,X3)),k5_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0)),k1_zfmisc_1(k2_xboole_0(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,plain,
    ( r1_tarski(k5_xboole_0(X1,k4_xboole_0(k1_zfmisc_1(X2),X3)),k1_zfmisc_1(k5_xboole_0(X2,k4_xboole_0(X4,X2))))
    | ~ r1_tarski(X1,k1_zfmisc_1(k5_xboole_0(X2,k4_xboole_0(X4,X2)))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_47])).

cnf(c_0_52,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(k5_xboole_0(X2,k4_xboole_0(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_45])).

cnf(c_0_53,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k5_xboole_0(X2,k4_xboole_0(X1,X3))
    | ~ r1_tarski(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k5_xboole_0(X2,k4_xboole_0(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k3_enumset1(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0))),k1_zfmisc_1(k3_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_55,plain,
    ( r1_tarski(k5_xboole_0(k1_zfmisc_1(X1),k4_xboole_0(k1_zfmisc_1(X2),X3)),k1_zfmisc_1(k5_xboole_0(X2,k4_xboole_0(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k5_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(esk1_0),k4_xboole_0(k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk1_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_28]),c_0_28])).

cnf(c_0_58,plain,
    ( r1_tarski(k5_xboole_0(k1_zfmisc_1(X1),k4_xboole_0(k1_zfmisc_1(X2),X3)),k1_zfmisc_1(k5_xboole_0(X1,k4_xboole_0(X2,X1)))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:35:59 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 35.16/35.35  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S081N
% 35.16/35.35  # and selection function SelectCQArNTNp.
% 35.16/35.35  #
% 35.16/35.35  # Preprocessing time       : 0.027 s
% 35.16/35.35  # Presaturation interreduction done
% 35.16/35.35  
% 35.16/35.35  # Proof found!
% 35.16/35.35  # SZS status Theorem
% 35.16/35.35  # SZS output start CNFRefutation
% 35.16/35.35  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 35.16/35.35  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 35.16/35.35  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 35.16/35.35  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 35.16/35.35  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 35.16/35.35  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 35.16/35.35  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 35.16/35.35  fof(t109_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 35.16/35.35  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 35.16/35.35  fof(t79_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 35.16/35.35  fof(t110_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k5_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_xboole_1)).
% 35.16/35.35  fof(t81_zfmisc_1, conjecture, ![X1, X2]:r1_tarski(k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)),k1_zfmisc_1(k2_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_zfmisc_1)).
% 35.16/35.35  fof(c_0_12, plain, ![X29, X30]:k3_tarski(k2_tarski(X29,X30))=k2_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 35.16/35.35  fof(c_0_13, plain, ![X20, X21]:k1_enumset1(X20,X20,X21)=k2_tarski(X20,X21), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 35.16/35.35  fof(c_0_14, plain, ![X16, X17]:r1_tarski(X16,k2_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 35.16/35.35  cnf(c_0_15, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 35.16/35.35  cnf(c_0_16, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 35.16/35.35  fof(c_0_17, plain, ![X22, X23, X24]:k2_enumset1(X22,X22,X23,X24)=k1_enumset1(X22,X23,X24), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 35.16/35.35  fof(c_0_18, plain, ![X25, X26, X27, X28]:k3_enumset1(X25,X25,X26,X27,X28)=k2_enumset1(X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 35.16/35.35  fof(c_0_19, plain, ![X18, X19]:k2_xboole_0(X18,X19)=k5_xboole_0(X18,k4_xboole_0(X19,X18)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 35.16/35.35  cnf(c_0_20, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 35.16/35.35  cnf(c_0_21, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 35.16/35.35  cnf(c_0_22, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 35.16/35.35  cnf(c_0_23, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 35.16/35.35  cnf(c_0_24, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 35.16/35.35  fof(c_0_25, plain, ![X10, X11, X12]:(~r1_tarski(X10,X11)|r1_tarski(X10,k2_xboole_0(X12,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 35.16/35.35  fof(c_0_26, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|r1_tarski(k4_xboole_0(X7,X9),X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_xboole_1])])).
% 35.16/35.35  cnf(c_0_27, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])).
% 35.16/35.35  cnf(c_0_28, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_21]), c_0_22]), c_0_23])).
% 35.16/35.35  cnf(c_0_29, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 35.16/35.35  fof(c_0_30, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 35.16/35.35  fof(c_0_31, plain, ![X31, X32]:(~r1_tarski(X31,X32)|r1_tarski(k1_zfmisc_1(X31),k1_zfmisc_1(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).
% 35.16/35.35  fof(c_0_32, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_tarski(X15,X14)|r1_tarski(k5_xboole_0(X13,X15),X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t110_xboole_1])])).
% 35.16/35.35  cnf(c_0_33, plain, (r1_tarski(k4_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 35.16/35.35  cnf(c_0_34, plain, (r1_tarski(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 35.16/35.35  cnf(c_0_35, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_21]), c_0_22]), c_0_23])).
% 35.16/35.35  cnf(c_0_36, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 35.16/35.35  cnf(c_0_37, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 35.16/35.35  cnf(c_0_38, plain, (r1_tarski(k5_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 35.16/35.35  cnf(c_0_39, plain, (r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,k4_xboole_0(X3,X1)))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 35.16/35.35  cnf(c_0_40, plain, (r1_tarski(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))|~r1_tarski(X1,X3)), inference(rw,[status(thm)],[c_0_35, c_0_28])).
% 35.16/35.35  cnf(c_0_41, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_36])).
% 35.16/35.35  fof(c_0_42, negated_conjecture, ~(![X1, X2]:r1_tarski(k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)),k1_zfmisc_1(k2_xboole_0(X1,X2)))), inference(assume_negation,[status(cth)],[t81_zfmisc_1])).
% 35.16/35.35  cnf(c_0_43, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(k5_xboole_0(X1,k4_xboole_0(X2,X1))))), inference(spm,[status(thm)],[c_0_37, c_0_34])).
% 35.16/35.35  cnf(c_0_44, plain, (r1_tarski(k5_xboole_0(X1,k4_xboole_0(X2,X3)),k5_xboole_0(X2,k4_xboole_0(X4,X2)))|~r1_tarski(X1,k5_xboole_0(X2,k4_xboole_0(X4,X2)))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 35.16/35.35  cnf(c_0_45, plain, (r1_tarski(X1,k5_xboole_0(X2,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 35.16/35.35  fof(c_0_46, negated_conjecture, ~r1_tarski(k2_xboole_0(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0)),k1_zfmisc_1(k2_xboole_0(esk1_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])).
% 35.16/35.35  cnf(c_0_47, plain, (r1_tarski(k4_xboole_0(k1_zfmisc_1(X1),X2),k1_zfmisc_1(k5_xboole_0(X1,k4_xboole_0(X3,X1))))), inference(spm,[status(thm)],[c_0_33, c_0_43])).
% 35.16/35.35  cnf(c_0_48, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 35.16/35.35  cnf(c_0_49, plain, (r1_tarski(k5_xboole_0(X1,k4_xboole_0(X2,X3)),k5_xboole_0(X2,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 35.16/35.35  cnf(c_0_50, negated_conjecture, (~r1_tarski(k2_xboole_0(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0)),k1_zfmisc_1(k2_xboole_0(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 35.16/35.35  cnf(c_0_51, plain, (r1_tarski(k5_xboole_0(X1,k4_xboole_0(k1_zfmisc_1(X2),X3)),k1_zfmisc_1(k5_xboole_0(X2,k4_xboole_0(X4,X2))))|~r1_tarski(X1,k1_zfmisc_1(k5_xboole_0(X2,k4_xboole_0(X4,X2))))), inference(spm,[status(thm)],[c_0_38, c_0_47])).
% 35.16/35.35  cnf(c_0_52, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(k5_xboole_0(X2,k4_xboole_0(X1,X2))))), inference(spm,[status(thm)],[c_0_37, c_0_45])).
% 35.16/35.35  cnf(c_0_53, plain, (k5_xboole_0(X1,k4_xboole_0(X2,X1))=k5_xboole_0(X2,k4_xboole_0(X1,X3))|~r1_tarski(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k5_xboole_0(X2,k4_xboole_0(X1,X3)))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 35.16/35.35  cnf(c_0_54, negated_conjecture, (~r1_tarski(k3_tarski(k3_enumset1(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0))),k1_zfmisc_1(k3_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_21]), c_0_21]), c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 35.16/35.35  cnf(c_0_55, plain, (r1_tarski(k5_xboole_0(k1_zfmisc_1(X1),k4_xboole_0(k1_zfmisc_1(X2),X3)),k1_zfmisc_1(k5_xboole_0(X2,k4_xboole_0(X1,X2))))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 35.16/35.35  cnf(c_0_56, plain, (k5_xboole_0(X1,k4_xboole_0(X2,X1))=k5_xboole_0(X2,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_53, c_0_49])).
% 35.16/35.35  cnf(c_0_57, negated_conjecture, (~r1_tarski(k5_xboole_0(k1_zfmisc_1(esk1_0),k4_xboole_0(k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk1_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_28]), c_0_28])).
% 35.16/35.35  cnf(c_0_58, plain, (r1_tarski(k5_xboole_0(k1_zfmisc_1(X1),k4_xboole_0(k1_zfmisc_1(X2),X3)),k1_zfmisc_1(k5_xboole_0(X1,k4_xboole_0(X2,X1))))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 35.16/35.35  cnf(c_0_59, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58])]), ['proof']).
% 35.16/35.35  # SZS output end CNFRefutation
% 35.16/35.35  # Proof object total steps             : 60
% 35.16/35.35  # Proof object clause steps            : 35
% 35.16/35.35  # Proof object formula steps           : 25
% 35.16/35.35  # Proof object conjectures             : 7
% 35.16/35.35  # Proof object clause conjectures      : 4
% 35.16/35.35  # Proof object formula conjectures     : 3
% 35.16/35.35  # Proof object initial clauses used    : 13
% 35.16/35.35  # Proof object initial formulas used   : 12
% 35.16/35.35  # Proof object generating inferences   : 12
% 35.16/35.35  # Proof object simplifying inferences  : 23
% 35.16/35.35  # Training examples: 0 positive, 0 negative
% 35.16/35.35  # Parsed axioms                        : 12
% 35.16/35.35  # Removed by relevancy pruning/SinE    : 0
% 35.16/35.35  # Initial clauses                      : 14
% 35.16/35.35  # Removed in clause preprocessing      : 4
% 35.16/35.35  # Initial clauses in saturation        : 10
% 35.16/35.35  # Processed clauses                    : 7487
% 35.16/35.35  # ...of these trivial                  : 355
% 35.16/35.35  # ...subsumed                          : 2888
% 35.16/35.35  # ...remaining for further processing  : 4244
% 35.16/35.35  # Other redundant clauses eliminated   : 2
% 35.16/35.35  # Clauses deleted for lack of memory   : 14977
% 35.16/35.35  # Backward-subsumed                    : 11
% 35.16/35.35  # Backward-rewritten                   : 10
% 35.16/35.35  # Generated clauses                    : 3189876
% 35.16/35.35  # ...of the previous two non-trivial   : 3173651
% 35.16/35.35  # Contextual simplify-reflections      : 0
% 35.16/35.35  # Paramodulations                      : 3189874
% 35.16/35.35  # Factorizations                       : 0
% 35.16/35.35  # Equation resolutions                 : 2
% 35.16/35.35  # Propositional unsat checks           : 0
% 35.16/35.35  #    Propositional check models        : 0
% 35.16/35.35  #    Propositional check unsatisfiable : 0
% 35.16/35.35  #    Propositional clauses             : 0
% 35.16/35.35  #    Propositional clauses after purity: 0
% 35.16/35.35  #    Propositional unsat core size     : 0
% 35.16/35.35  #    Propositional preprocessing time  : 0.000
% 35.16/35.35  #    Propositional encoding time       : 0.000
% 35.16/35.35  #    Propositional solver time         : 0.000
% 35.16/35.35  #    Success case prop preproc time    : 0.000
% 35.16/35.35  #    Success case prop encoding time   : 0.000
% 35.16/35.35  #    Success case prop solver time     : 0.000
% 35.16/35.35  # Current number of processed clauses  : 4212
% 35.16/35.35  #    Positive orientable unit clauses  : 2452
% 35.16/35.35  #    Positive unorientable unit clauses: 1
% 35.16/35.35  #    Negative unit clauses             : 0
% 35.16/35.35  #    Non-unit-clauses                  : 1759
% 35.16/35.35  # Current number of unprocessed clauses: 1131218
% 35.16/35.35  # ...number of literals in the above   : 1137252
% 35.16/35.35  # Current number of archived formulas  : 0
% 35.16/35.35  # Current number of archived clauses   : 34
% 35.16/35.35  # Clause-clause subsumption calls (NU) : 271867
% 35.16/35.35  # Rec. Clause-clause subsumption calls : 263281
% 35.16/35.35  # Non-unit clause-clause subsumptions  : 2897
% 35.16/35.35  # Unit Clause-clause subsumption calls : 114560
% 35.16/35.35  # Rewrite failures with RHS unbound    : 0
% 35.16/35.35  # BW rewrite match attempts            : 333436
% 35.16/35.35  # BW rewrite match successes           : 115
% 35.16/35.35  # Condensation attempts                : 0
% 35.16/35.35  # Condensation successes               : 0
% 35.16/35.35  # Termbank termtop insertions          : 125457392
% 35.21/35.43  
% 35.21/35.43  # -------------------------------------------------
% 35.21/35.43  # User time                : 33.996 s
% 35.21/35.43  # System time              : 1.077 s
% 35.21/35.43  # Total time               : 35.073 s
% 35.21/35.43  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
