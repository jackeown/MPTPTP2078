%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:12 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   40 (  71 expanded)
%              Number of clauses        :   21 (  32 expanded)
%              Number of leaves         :    9 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :   56 (  90 expanded)
%              Number of equality atoms :   16 (  40 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t86_zfmisc_1,conjecture,(
    ! [X1,X2] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X1,X2)),k1_zfmisc_1(k4_xboole_0(X2,X1))),k1_zfmisc_1(k5_xboole_0(X1,X2))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_zfmisc_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(t83_zfmisc_1,axiom,(
    ! [X1,X2] : k1_zfmisc_1(k3_xboole_0(X1,X2)) = k3_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_zfmisc_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t96_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).

fof(t79_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X1,X2)),k1_zfmisc_1(k4_xboole_0(X2,X1))),k1_zfmisc_1(k5_xboole_0(X1,X2))) ),
    inference(assume_negation,[status(cth)],[t86_zfmisc_1])).

fof(c_0_10,negated_conjecture,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(esk1_0,esk2_0)),k1_zfmisc_1(k4_xboole_0(esk2_0,esk1_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_11,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_12,plain,(
    ! [X24,X25] : k2_xboole_0(X24,X25) = k5_xboole_0(k5_xboole_0(X24,X25),k3_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

fof(c_0_13,plain,(
    ! [X17,X18,X19] :
      ( ~ r1_tarski(X17,X18)
      | ~ r1_tarski(X19,X18)
      | r1_tarski(k2_xboole_0(X17,X19),X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_14,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(esk1_0,esk2_0)),k1_zfmisc_1(k4_xboole_0(esk2_0,esk1_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X30,X31] : k1_zfmisc_1(k3_xboole_0(X30,X31)) = k3_xboole_0(k1_zfmisc_1(X30),k1_zfmisc_1(X31)) ),
    inference(variable_rename,[status(thm)],[t83_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k5_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_19,plain,(
    ! [X20,X21,X22] : k5_xboole_0(k5_xboole_0(X20,X21),X22) = k5_xboole_0(X20,k5_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_20,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk1_0)))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk1_0))))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_15]),c_0_16])).

cnf(c_0_22,plain,
    ( k1_zfmisc_1(k3_xboole_0(X1,X2)) = k3_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(X1,X3),k3_xboole_0(X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_16])).

fof(c_0_26,plain,(
    ! [X26,X27] : r1_tarski(k4_xboole_0(X26,X27),k5_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t96_xboole_1])).

cnf(c_0_27,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk1_0)))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk1_0))))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_28,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( r1_tarski(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))),X3)
    | ~ r1_tarski(X2,X3)
    | ~ r1_tarski(X1,X3) ),
    inference(rw,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_30,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk1_0))),k1_zfmisc_1(k3_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk1_0)))))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( r1_tarski(k5_xboole_0(k1_zfmisc_1(X1),k5_xboole_0(k1_zfmisc_1(X2),k1_zfmisc_1(k3_xboole_0(X1,X2)))),X3)
    | ~ r1_tarski(k1_zfmisc_1(X2),X3)
    | ~ r1_tarski(k1_zfmisc_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_29,c_0_22])).

fof(c_0_33,plain,(
    ! [X28,X29] :
      ( ~ r1_tarski(X28,X29)
      | r1_tarski(k1_zfmisc_1(X28),k1_zfmisc_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).

cnf(c_0_34,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk1_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0)))
    | ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_23])).

cnf(c_0_38,negated_conjecture,
    ( ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_36]),c_0_34])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:00:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.44  # AutoSched0-Mode selected heuristic G_E___208_C12_11_nc_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.44  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.44  #
% 0.19/0.44  # Preprocessing time       : 0.027 s
% 0.19/0.44  # Presaturation interreduction done
% 0.19/0.44  
% 0.19/0.44  # Proof found!
% 0.19/0.44  # SZS status Theorem
% 0.19/0.44  # SZS output start CNFRefutation
% 0.19/0.44  fof(t86_zfmisc_1, conjecture, ![X1, X2]:r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X1,X2)),k1_zfmisc_1(k4_xboole_0(X2,X1))),k1_zfmisc_1(k5_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_zfmisc_1)).
% 0.19/0.44  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.44  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.19/0.44  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.19/0.44  fof(t83_zfmisc_1, axiom, ![X1, X2]:k1_zfmisc_1(k3_xboole_0(X1,X2))=k3_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_zfmisc_1)).
% 0.19/0.44  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.19/0.44  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.19/0.44  fof(t96_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_xboole_1)).
% 0.19/0.44  fof(t79_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 0.19/0.44  fof(c_0_9, negated_conjecture, ~(![X1, X2]:r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X1,X2)),k1_zfmisc_1(k4_xboole_0(X2,X1))),k1_zfmisc_1(k5_xboole_0(X1,X2)))), inference(assume_negation,[status(cth)],[t86_zfmisc_1])).
% 0.19/0.44  fof(c_0_10, negated_conjecture, ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(esk1_0,esk2_0)),k1_zfmisc_1(k4_xboole_0(esk2_0,esk1_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.19/0.44  fof(c_0_11, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.44  fof(c_0_12, plain, ![X24, X25]:k2_xboole_0(X24,X25)=k5_xboole_0(k5_xboole_0(X24,X25),k3_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.19/0.44  fof(c_0_13, plain, ![X17, X18, X19]:(~r1_tarski(X17,X18)|~r1_tarski(X19,X18)|r1_tarski(k2_xboole_0(X17,X19),X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.19/0.44  cnf(c_0_14, negated_conjecture, (~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(esk1_0,esk2_0)),k1_zfmisc_1(k4_xboole_0(esk2_0,esk1_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.44  cnf(c_0_15, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.44  cnf(c_0_16, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.44  fof(c_0_17, plain, ![X30, X31]:k1_zfmisc_1(k3_xboole_0(X30,X31))=k3_xboole_0(k1_zfmisc_1(X30),k1_zfmisc_1(X31)), inference(variable_rename,[status(thm)],[t83_zfmisc_1])).
% 0.19/0.44  fof(c_0_18, plain, ![X6, X7]:k5_xboole_0(X6,X7)=k5_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.19/0.44  fof(c_0_19, plain, ![X20, X21, X22]:k5_xboole_0(k5_xboole_0(X20,X21),X22)=k5_xboole_0(X20,k5_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.19/0.44  cnf(c_0_20, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.44  cnf(c_0_21, negated_conjecture, (~r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk1_0)))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk1_0))))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_15]), c_0_15]), c_0_16])).
% 0.19/0.44  cnf(c_0_22, plain, (k1_zfmisc_1(k3_xboole_0(X1,X2))=k3_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.44  cnf(c_0_23, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.44  cnf(c_0_24, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.44  cnf(c_0_25, plain, (r1_tarski(k5_xboole_0(k5_xboole_0(X1,X3),k3_xboole_0(X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_16])).
% 0.19/0.44  fof(c_0_26, plain, ![X26, X27]:r1_tarski(k4_xboole_0(X26,X27),k5_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t96_xboole_1])).
% 0.19/0.44  cnf(c_0_27, negated_conjecture, (~r1_tarski(k5_xboole_0(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk1_0)))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk1_0))))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.19/0.44  cnf(c_0_28, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X3,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.44  cnf(c_0_29, plain, (r1_tarski(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))),X3)|~r1_tarski(X2,X3)|~r1_tarski(X1,X3)), inference(rw,[status(thm)],[c_0_25, c_0_24])).
% 0.19/0.44  cnf(c_0_30, plain, (r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.44  cnf(c_0_31, negated_conjecture, (~r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk1_0))),k1_zfmisc_1(k3_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk1_0)))))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0)))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.44  cnf(c_0_32, plain, (r1_tarski(k5_xboole_0(k1_zfmisc_1(X1),k5_xboole_0(k1_zfmisc_1(X2),k1_zfmisc_1(k3_xboole_0(X1,X2)))),X3)|~r1_tarski(k1_zfmisc_1(X2),X3)|~r1_tarski(k1_zfmisc_1(X1),X3)), inference(spm,[status(thm)],[c_0_29, c_0_22])).
% 0.19/0.44  fof(c_0_33, plain, ![X28, X29]:(~r1_tarski(X28,X29)|r1_tarski(k1_zfmisc_1(X28),k1_zfmisc_1(X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).
% 0.19/0.44  cnf(c_0_34, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_30, c_0_15])).
% 0.19/0.44  cnf(c_0_35, negated_conjecture, (~r1_tarski(k1_zfmisc_1(k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk1_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0)))|~r1_tarski(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.44  cnf(c_0_36, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.44  cnf(c_0_37, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_34, c_0_23])).
% 0.19/0.44  cnf(c_0_38, negated_conjecture, (~r1_tarski(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])])).
% 0.19/0.44  cnf(c_0_39, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_36]), c_0_34])]), ['proof']).
% 0.19/0.44  # SZS output end CNFRefutation
% 0.19/0.44  # Proof object total steps             : 40
% 0.19/0.44  # Proof object clause steps            : 21
% 0.19/0.44  # Proof object formula steps           : 19
% 0.19/0.44  # Proof object conjectures             : 10
% 0.19/0.44  # Proof object clause conjectures      : 7
% 0.19/0.44  # Proof object formula conjectures     : 3
% 0.19/0.44  # Proof object initial clauses used    : 9
% 0.19/0.44  # Proof object initial formulas used   : 9
% 0.19/0.44  # Proof object generating inferences   : 6
% 0.19/0.44  # Proof object simplifying inferences  : 13
% 0.19/0.44  # Training examples: 0 positive, 0 negative
% 0.19/0.44  # Parsed axioms                        : 15
% 0.19/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.44  # Initial clauses                      : 15
% 0.19/0.44  # Removed in clause preprocessing      : 2
% 0.19/0.44  # Initial clauses in saturation        : 13
% 0.19/0.44  # Processed clauses                    : 673
% 0.19/0.44  # ...of these trivial                  : 37
% 0.19/0.44  # ...subsumed                          : 414
% 0.19/0.44  # ...remaining for further processing  : 222
% 0.19/0.44  # Other redundant clauses eliminated   : 0
% 0.19/0.44  # Clauses deleted for lack of memory   : 0
% 0.19/0.44  # Backward-subsumed                    : 22
% 0.19/0.44  # Backward-rewritten                   : 82
% 0.19/0.44  # Generated clauses                    : 3002
% 0.19/0.44  # ...of the previous two non-trivial   : 2440
% 0.19/0.44  # Contextual simplify-reflections      : 4
% 0.19/0.44  # Paramodulations                      : 3002
% 0.19/0.44  # Factorizations                       : 0
% 0.19/0.44  # Equation resolutions                 : 0
% 0.19/0.44  # Propositional unsat checks           : 0
% 0.19/0.44  #    Propositional check models        : 0
% 0.19/0.44  #    Propositional check unsatisfiable : 0
% 0.19/0.44  #    Propositional clauses             : 0
% 0.19/0.44  #    Propositional clauses after purity: 0
% 0.19/0.44  #    Propositional unsat core size     : 0
% 0.19/0.44  #    Propositional preprocessing time  : 0.000
% 0.19/0.44  #    Propositional encoding time       : 0.000
% 0.19/0.44  #    Propositional solver time         : 0.000
% 0.19/0.44  #    Success case prop preproc time    : 0.000
% 0.19/0.44  #    Success case prop encoding time   : 0.000
% 0.19/0.44  #    Success case prop solver time     : 0.000
% 0.19/0.44  # Current number of processed clauses  : 105
% 0.19/0.44  #    Positive orientable unit clauses  : 23
% 0.19/0.44  #    Positive unorientable unit clauses: 7
% 0.19/0.44  #    Negative unit clauses             : 7
% 0.19/0.44  #    Non-unit-clauses                  : 68
% 0.19/0.44  # Current number of unprocessed clauses: 1700
% 0.19/0.44  # ...number of literals in the above   : 3528
% 0.19/0.44  # Current number of archived formulas  : 0
% 0.19/0.44  # Current number of archived clauses   : 119
% 0.19/0.44  # Clause-clause subsumption calls (NU) : 4441
% 0.19/0.44  # Rec. Clause-clause subsumption calls : 2811
% 0.19/0.44  # Non-unit clause-clause subsumptions  : 322
% 0.19/0.44  # Unit Clause-clause subsumption calls : 169
% 0.19/0.44  # Rewrite failures with RHS unbound    : 0
% 0.19/0.44  # BW rewrite match attempts            : 340
% 0.19/0.44  # BW rewrite match successes           : 121
% 0.19/0.44  # Condensation attempts                : 0
% 0.19/0.44  # Condensation successes               : 0
% 0.19/0.44  # Termbank termtop insertions          : 42980
% 0.19/0.44  
% 0.19/0.44  # -------------------------------------------------
% 0.19/0.44  # User time                : 0.089 s
% 0.19/0.44  # System time              : 0.005 s
% 0.19/0.44  # Total time               : 0.094 s
% 0.19/0.44  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
