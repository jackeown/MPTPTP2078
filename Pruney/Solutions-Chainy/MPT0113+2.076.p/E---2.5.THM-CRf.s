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
% DateTime   : Thu Dec  3 10:34:45 EST 2020

% Result     : Theorem 0.38s
% Output     : CNFRefutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   42 (  99 expanded)
%              Number of clauses        :   25 (  42 expanded)
%              Number of leaves         :    8 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :   70 ( 165 expanded)
%              Number of equality atoms :   14 (  56 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t106_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,k4_xboole_0(X2,X3))
       => ( r1_tarski(X1,X2)
          & r1_xboole_0(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t106_xboole_1])).

fof(c_0_9,plain,(
    ! [X14,X15] : r1_tarski(k4_xboole_0(X14,X15),X14) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_10,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_11,plain,(
    ! [X21,X22] : k3_xboole_0(X21,X22) = k5_xboole_0(k5_xboole_0(X21,X22),k2_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

fof(c_0_12,negated_conjecture,
    ( r1_tarski(esk2_0,k4_xboole_0(esk3_0,esk4_0))
    & ( ~ r1_tarski(esk2_0,esk3_0)
      | ~ r1_xboole_0(esk2_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_13,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_14,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk2_0,k4_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r1_tarski(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(esk2_0,k5_xboole_0(esk3_0,k5_xboole_0(k5_xboole_0(esk3_0,esk4_0),k2_xboole_0(esk3_0,esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_15]),c_0_16])).

fof(c_0_21,plain,(
    ! [X19,X20] : r1_xboole_0(k4_xboole_0(X19,X20),X20) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_22,plain,(
    ! [X16,X17,X18] : k3_xboole_0(X16,k4_xboole_0(X17,X18)) = k4_xboole_0(k3_xboole_0(X16,X17),X18) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(X1,k5_xboole_0(esk3_0,k5_xboole_0(k5_xboole_0(esk3_0,esk4_0),k2_xboole_0(esk3_0,esk4_0))))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_20])).

cnf(c_0_25,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_27,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,X13)
      | k3_xboole_0(X12,X13) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_15]),c_0_16])).

cnf(c_0_31,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))),k2_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)),X3),k2_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)),X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_15]),c_0_15]),c_0_16]),c_0_16]),c_0_16]),c_0_16]),c_0_16])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r2_hidden(esk1_2(X1,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_35,plain,
    ( r1_xboole_0(k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))),k2_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))))),X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_32,c_0_16])).

cnf(c_0_37,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk3_0)
    | ~ r1_xboole_0(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X3,X2),k2_xboole_0(X3,X2)))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38])])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_20]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:27:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.38/0.53  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 0.38/0.53  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.38/0.53  #
% 0.38/0.53  # Preprocessing time       : 0.027 s
% 0.38/0.53  # Presaturation interreduction done
% 0.38/0.53  
% 0.38/0.53  # Proof found!
% 0.38/0.53  # SZS status Theorem
% 0.38/0.53  # SZS output start CNFRefutation
% 0.38/0.53  fof(t106_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.38/0.53  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.38/0.53  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.38/0.53  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.38/0.53  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.38/0.53  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.38/0.53  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.38/0.53  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.38/0.53  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3)))), inference(assume_negation,[status(cth)],[t106_xboole_1])).
% 0.38/0.53  fof(c_0_9, plain, ![X14, X15]:r1_tarski(k4_xboole_0(X14,X15),X14), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.38/0.53  fof(c_0_10, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.38/0.53  fof(c_0_11, plain, ![X21, X22]:k3_xboole_0(X21,X22)=k5_xboole_0(k5_xboole_0(X21,X22),k2_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.38/0.53  fof(c_0_12, negated_conjecture, (r1_tarski(esk2_0,k4_xboole_0(esk3_0,esk4_0))&(~r1_tarski(esk2_0,esk3_0)|~r1_xboole_0(esk2_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.38/0.53  fof(c_0_13, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.38/0.53  cnf(c_0_14, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.38/0.53  cnf(c_0_15, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.38/0.53  cnf(c_0_16, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.38/0.53  cnf(c_0_17, negated_conjecture, (r1_tarski(esk2_0,k4_xboole_0(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.38/0.53  cnf(c_0_18, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.38/0.53  cnf(c_0_19, plain, (r1_tarski(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 0.38/0.53  cnf(c_0_20, negated_conjecture, (r1_tarski(esk2_0,k5_xboole_0(esk3_0,k5_xboole_0(k5_xboole_0(esk3_0,esk4_0),k2_xboole_0(esk3_0,esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_15]), c_0_16])).
% 0.38/0.53  fof(c_0_21, plain, ![X19, X20]:r1_xboole_0(k4_xboole_0(X19,X20),X20), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.38/0.53  fof(c_0_22, plain, ![X16, X17, X18]:k3_xboole_0(X16,k4_xboole_0(X17,X18))=k4_xboole_0(k3_xboole_0(X16,X17),X18), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.38/0.53  cnf(c_0_23, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.38/0.53  cnf(c_0_24, negated_conjecture, (r2_hidden(X1,k5_xboole_0(esk3_0,k5_xboole_0(k5_xboole_0(esk3_0,esk4_0),k2_xboole_0(esk3_0,esk4_0))))|~r2_hidden(X1,esk2_0)), inference(spm,[status(thm)],[c_0_18, c_0_20])).
% 0.38/0.53  cnf(c_0_25, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.38/0.53  cnf(c_0_26, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.38/0.53  fof(c_0_27, plain, ![X12, X13]:(~r1_tarski(X12,X13)|k3_xboole_0(X12,X13)=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.38/0.53  cnf(c_0_28, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.38/0.53  cnf(c_0_29, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk2_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.38/0.53  cnf(c_0_30, plain, (r1_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_15]), c_0_16])).
% 0.38/0.53  cnf(c_0_31, plain, (k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))),k2_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))))=k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)),X3),k2_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)),X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_15]), c_0_15]), c_0_16]), c_0_16]), c_0_16]), c_0_16]), c_0_16])).
% 0.38/0.53  cnf(c_0_32, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.38/0.53  cnf(c_0_33, negated_conjecture, (r1_tarski(X1,esk3_0)|~r2_hidden(esk1_2(X1,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.38/0.53  cnf(c_0_34, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.38/0.53  cnf(c_0_35, plain, (r1_xboole_0(k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))),k2_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))))),X3)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.38/0.53  cnf(c_0_36, plain, (k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_32, c_0_16])).
% 0.38/0.53  cnf(c_0_37, negated_conjecture, (~r1_tarski(esk2_0,esk3_0)|~r1_xboole_0(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.38/0.53  cnf(c_0_38, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.38/0.53  cnf(c_0_39, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X3,X2),k2_xboole_0(X3,X2))))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.38/0.53  cnf(c_0_40, negated_conjecture, (~r1_xboole_0(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38])])).
% 0.38/0.53  cnf(c_0_41, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_20]), c_0_40]), ['proof']).
% 0.38/0.53  # SZS output end CNFRefutation
% 0.38/0.53  # Proof object total steps             : 42
% 0.38/0.53  # Proof object clause steps            : 25
% 0.38/0.53  # Proof object formula steps           : 17
% 0.38/0.53  # Proof object conjectures             : 12
% 0.38/0.53  # Proof object clause conjectures      : 9
% 0.38/0.53  # Proof object formula conjectures     : 3
% 0.38/0.53  # Proof object initial clauses used    : 11
% 0.38/0.53  # Proof object initial formulas used   : 8
% 0.38/0.53  # Proof object generating inferences   : 8
% 0.38/0.53  # Proof object simplifying inferences  : 17
% 0.38/0.53  # Training examples: 0 positive, 0 negative
% 0.38/0.53  # Parsed axioms                        : 8
% 0.38/0.53  # Removed by relevancy pruning/SinE    : 0
% 0.38/0.53  # Initial clauses                      : 11
% 0.38/0.53  # Removed in clause preprocessing      : 2
% 0.38/0.53  # Initial clauses in saturation        : 9
% 0.38/0.53  # Processed clauses                    : 140
% 0.38/0.53  # ...of these trivial                  : 0
% 0.38/0.53  # ...subsumed                          : 32
% 0.38/0.53  # ...remaining for further processing  : 108
% 0.38/0.53  # Other redundant clauses eliminated   : 0
% 0.38/0.53  # Clauses deleted for lack of memory   : 0
% 0.38/0.53  # Backward-subsumed                    : 10
% 0.38/0.53  # Backward-rewritten                   : 4
% 0.38/0.53  # Generated clauses                    : 1717
% 0.38/0.53  # ...of the previous two non-trivial   : 1681
% 0.38/0.53  # Contextual simplify-reflections      : 0
% 0.38/0.53  # Paramodulations                      : 1717
% 0.38/0.53  # Factorizations                       : 0
% 0.38/0.53  # Equation resolutions                 : 0
% 0.38/0.53  # Propositional unsat checks           : 0
% 0.38/0.53  #    Propositional check models        : 0
% 0.38/0.53  #    Propositional check unsatisfiable : 0
% 0.38/0.53  #    Propositional clauses             : 0
% 0.38/0.53  #    Propositional clauses after purity: 0
% 0.38/0.53  #    Propositional unsat core size     : 0
% 0.38/0.53  #    Propositional preprocessing time  : 0.000
% 0.38/0.53  #    Propositional encoding time       : 0.000
% 0.38/0.53  #    Propositional solver time         : 0.000
% 0.38/0.53  #    Success case prop preproc time    : 0.000
% 0.38/0.53  #    Success case prop encoding time   : 0.000
% 0.38/0.53  #    Success case prop solver time     : 0.000
% 0.38/0.53  # Current number of processed clauses  : 85
% 0.38/0.53  #    Positive orientable unit clauses  : 25
% 0.38/0.53  #    Positive unorientable unit clauses: 4
% 0.38/0.53  #    Negative unit clauses             : 1
% 0.38/0.53  #    Non-unit-clauses                  : 55
% 0.38/0.53  # Current number of unprocessed clauses: 1526
% 0.38/0.53  # ...number of literals in the above   : 2667
% 0.38/0.53  # Current number of archived formulas  : 0
% 0.38/0.53  # Current number of archived clauses   : 25
% 0.38/0.53  # Clause-clause subsumption calls (NU) : 575
% 0.38/0.53  # Rec. Clause-clause subsumption calls : 472
% 0.38/0.53  # Non-unit clause-clause subsumptions  : 41
% 0.38/0.53  # Unit Clause-clause subsumption calls : 49
% 0.38/0.53  # Rewrite failures with RHS unbound    : 0
% 0.38/0.53  # BW rewrite match attempts            : 64
% 0.38/0.53  # BW rewrite match successes           : 5
% 0.38/0.53  # Condensation attempts                : 0
% 0.38/0.53  # Condensation successes               : 0
% 0.38/0.53  # Termbank termtop insertions          : 474884
% 0.38/0.54  
% 0.38/0.54  # -------------------------------------------------
% 0.38/0.54  # User time                : 0.189 s
% 0.38/0.54  # System time              : 0.003 s
% 0.38/0.54  # Total time               : 0.191 s
% 0.38/0.54  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
