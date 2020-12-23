%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:54 EST 2020

% Result     : Theorem 0.54s
% Output     : CNFRefutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   48 (1785 expanded)
%              Number of clauses        :   35 ( 878 expanded)
%              Number of leaves         :    6 ( 453 expanded)
%              Depth                    :   18
%              Number of atoms          :   77 (6128 expanded)
%              Number of equality atoms :   52 (2644 expanded)
%              Maximal formula depth    :   17 (   2 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t23_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t24_xboole_1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).

fof(c_0_6,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( r2_hidden(X12,X9)
        | ~ r2_hidden(X12,X11)
        | X11 != k3_xboole_0(X9,X10) )
      & ( r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | X11 != k3_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X13,X9)
        | ~ r2_hidden(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k3_xboole_0(X9,X10) )
      & ( ~ r2_hidden(esk1_3(X14,X15,X16),X16)
        | ~ r2_hidden(esk1_3(X14,X15,X16),X14)
        | ~ r2_hidden(esk1_3(X14,X15,X16),X15)
        | X16 = k3_xboole_0(X14,X15) )
      & ( r2_hidden(esk1_3(X14,X15,X16),X14)
        | r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k3_xboole_0(X14,X15) )
      & ( r2_hidden(esk1_3(X14,X15,X16),X15)
        | r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k3_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_8,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X20,X21,X22] : k3_xboole_0(X20,k2_xboole_0(X21,X22)) = k2_xboole_0(k3_xboole_0(X20,X21),k3_xboole_0(X20,X22)) ),
    inference(variable_rename,[status(thm)],[t23_xboole_1])).

cnf(c_0_11,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r2_hidden(esk1_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_9])).

fof(c_0_12,plain,(
    ! [X18,X19] : k2_xboole_0(X18,k3_xboole_0(X18,X19)) = X18 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

fof(c_0_13,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_14,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_11,c_0_9])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_18])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_16,c_0_18])).

cnf(c_0_24,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X1),X3)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_22]),c_0_16])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_22]),c_0_20])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X1,X3))) = k3_xboole_0(k2_xboole_0(X1,X3),k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_19]),c_0_20])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_19]),c_0_16])).

cnf(c_0_30,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_18])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k2_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_29]),c_0_20])).

cnf(c_0_32,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X3,X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_23])).

cnf(c_0_33,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k2_xboole_0(X2,X3),X1)) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_32])).

cnf(c_0_35,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) = k2_xboole_0(X3,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_33]),c_0_33])).

cnf(c_0_36,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X3,X2)) = k2_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_34])).

cnf(c_0_37,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X3,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_35]),c_0_35])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X3,X1))) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_39,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    inference(assume_negation,[status(cth)],[t24_xboole_1])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,k2_xboole_0(k3_xboole_0(X2,X1),X3)) = k2_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_20])).

fof(c_0_41,negated_conjecture,(
    k2_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk4_0)) != k3_xboole_0(k2_xboole_0(esk2_0,esk3_0),k2_xboole_0(esk2_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).

cnf(c_0_42,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(k3_xboole_0(X2,X3),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_14])).

cnf(c_0_43,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1)) = k2_xboole_0(k3_xboole_0(X3,X2),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_14]),c_0_27])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,k3_xboole_0(k2_xboole_0(X1,X2),X3)) = k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_19])).

cnf(c_0_45,negated_conjecture,
    ( k2_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk4_0)) != k3_xboole_0(k2_xboole_0(esk2_0,esk3_0),k2_xboole_0(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) = k2_xboole_0(k3_xboole_0(X3,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_26]),c_0_20]),c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_18]),c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:16:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.54/0.75  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.54/0.75  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.54/0.75  #
% 0.54/0.75  # Preprocessing time       : 0.026 s
% 0.54/0.75  # Presaturation interreduction done
% 0.54/0.75  
% 0.54/0.75  # Proof found!
% 0.54/0.75  # SZS status Theorem
% 0.54/0.75  # SZS output start CNFRefutation
% 0.54/0.75  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.54/0.75  fof(t23_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 0.54/0.75  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.54/0.75  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.54/0.75  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.54/0.75  fof(t24_xboole_1, conjecture, ![X1, X2, X3]:k2_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_xboole_1)).
% 0.54/0.75  fof(c_0_6, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:((((r2_hidden(X12,X9)|~r2_hidden(X12,X11)|X11!=k3_xboole_0(X9,X10))&(r2_hidden(X12,X10)|~r2_hidden(X12,X11)|X11!=k3_xboole_0(X9,X10)))&(~r2_hidden(X13,X9)|~r2_hidden(X13,X10)|r2_hidden(X13,X11)|X11!=k3_xboole_0(X9,X10)))&((~r2_hidden(esk1_3(X14,X15,X16),X16)|(~r2_hidden(esk1_3(X14,X15,X16),X14)|~r2_hidden(esk1_3(X14,X15,X16),X15))|X16=k3_xboole_0(X14,X15))&((r2_hidden(esk1_3(X14,X15,X16),X14)|r2_hidden(esk1_3(X14,X15,X16),X16)|X16=k3_xboole_0(X14,X15))&(r2_hidden(esk1_3(X14,X15,X16),X15)|r2_hidden(esk1_3(X14,X15,X16),X16)|X16=k3_xboole_0(X14,X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.54/0.75  cnf(c_0_7, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.54/0.75  cnf(c_0_8, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.54/0.75  cnf(c_0_9, plain, (k3_xboole_0(X1,X2)=X2|r2_hidden(esk1_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_7])).
% 0.54/0.75  fof(c_0_10, plain, ![X20, X21, X22]:k3_xboole_0(X20,k2_xboole_0(X21,X22))=k2_xboole_0(k3_xboole_0(X20,X21),k3_xboole_0(X20,X22)), inference(variable_rename,[status(thm)],[t23_xboole_1])).
% 0.54/0.75  cnf(c_0_11, plain, (k3_xboole_0(X1,X2)=X2|~r2_hidden(esk1_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_9])).
% 0.54/0.75  fof(c_0_12, plain, ![X18, X19]:k2_xboole_0(X18,k3_xboole_0(X18,X19))=X18, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.54/0.75  fof(c_0_13, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.54/0.75  cnf(c_0_14, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.54/0.75  cnf(c_0_15, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_11, c_0_9])).
% 0.54/0.75  cnf(c_0_16, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.54/0.75  fof(c_0_17, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.54/0.75  cnf(c_0_18, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.54/0.75  cnf(c_0_19, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 0.54/0.75  cnf(c_0_20, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.54/0.75  cnf(c_0_21, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3))=k3_xboole_0(X2,k2_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_14, c_0_18])).
% 0.54/0.75  cnf(c_0_22, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.54/0.75  cnf(c_0_23, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_16, c_0_18])).
% 0.54/0.75  cnf(c_0_24, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(X2,k2_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_21, c_0_18])).
% 0.54/0.75  cnf(c_0_25, plain, (k3_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X1),X3))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_22]), c_0_16])).
% 0.54/0.75  cnf(c_0_26, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_22]), c_0_20])).
% 0.54/0.75  cnf(c_0_27, plain, (k2_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X1,X3)))=k3_xboole_0(k2_xboole_0(X1,X3),k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_19]), c_0_20])).
% 0.54/0.75  cnf(c_0_28, plain, (k3_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1)))=X1), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.54/0.75  cnf(c_0_29, plain, (k3_xboole_0(X1,k2_xboole_0(k2_xboole_0(X1,X2),X3))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_19]), c_0_16])).
% 0.54/0.75  cnf(c_0_30, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_18])).
% 0.54/0.75  cnf(c_0_31, plain, (k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X1,X2),X3))=k2_xboole_0(k2_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_29]), c_0_20])).
% 0.54/0.75  cnf(c_0_32, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X3,X2))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_23])).
% 0.54/0.75  cnf(c_0_33, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k2_xboole_0(X2,X3),X1))=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.54/0.75  cnf(c_0_34, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_23, c_0_32])).
% 0.54/0.75  cnf(c_0_35, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))=k2_xboole_0(X3,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_33]), c_0_33])).
% 0.54/0.75  cnf(c_0_36, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X3,X2))=k2_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_20, c_0_34])).
% 0.54/0.75  cnf(c_0_37, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(X3,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_35]), c_0_35])).
% 0.54/0.75  cnf(c_0_38, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X3,X1)))=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.54/0.75  fof(c_0_39, negated_conjecture, ~(![X1, X2, X3]:k2_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))), inference(assume_negation,[status(cth)],[t24_xboole_1])).
% 0.54/0.75  cnf(c_0_40, plain, (k2_xboole_0(X1,k2_xboole_0(k3_xboole_0(X2,X1),X3))=k2_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_38, c_0_20])).
% 0.54/0.75  fof(c_0_41, negated_conjecture, k2_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk4_0))!=k3_xboole_0(k2_xboole_0(esk2_0,esk3_0),k2_xboole_0(esk2_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).
% 0.54/0.75  cnf(c_0_42, plain, (k2_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(k3_xboole_0(X2,X3),X1)), inference(spm,[status(thm)],[c_0_38, c_0_14])).
% 0.54/0.75  cnf(c_0_43, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1))=k2_xboole_0(k3_xboole_0(X3,X2),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_14]), c_0_27])).
% 0.54/0.75  cnf(c_0_44, plain, (k2_xboole_0(X1,k3_xboole_0(k2_xboole_0(X1,X2),X3))=k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_21, c_0_19])).
% 0.54/0.75  cnf(c_0_45, negated_conjecture, (k2_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk4_0))!=k3_xboole_0(k2_xboole_0(esk2_0,esk3_0),k2_xboole_0(esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.54/0.75  cnf(c_0_46, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))=k2_xboole_0(k3_xboole_0(X3,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_26]), c_0_20]), c_0_44])).
% 0.54/0.75  cnf(c_0_47, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_18]), c_0_20])]), ['proof']).
% 0.54/0.75  # SZS output end CNFRefutation
% 0.54/0.75  # Proof object total steps             : 48
% 0.54/0.75  # Proof object clause steps            : 35
% 0.54/0.75  # Proof object formula steps           : 13
% 0.54/0.75  # Proof object conjectures             : 5
% 0.54/0.75  # Proof object clause conjectures      : 2
% 0.54/0.75  # Proof object formula conjectures     : 3
% 0.54/0.75  # Proof object initial clauses used    : 7
% 0.54/0.75  # Proof object initial formulas used   : 6
% 0.54/0.75  # Proof object generating inferences   : 26
% 0.54/0.75  # Proof object simplifying inferences  : 19
% 0.54/0.75  # Training examples: 0 positive, 0 negative
% 0.54/0.75  # Parsed axioms                        : 6
% 0.54/0.75  # Removed by relevancy pruning/SinE    : 0
% 0.54/0.75  # Initial clauses                      : 11
% 0.54/0.75  # Removed in clause preprocessing      : 0
% 0.54/0.75  # Initial clauses in saturation        : 11
% 0.54/0.75  # Processed clauses                    : 4027
% 0.54/0.75  # ...of these trivial                  : 724
% 0.54/0.75  # ...subsumed                          : 2936
% 0.54/0.75  # ...remaining for further processing  : 367
% 0.54/0.75  # Other redundant clauses eliminated   : 3
% 0.54/0.75  # Clauses deleted for lack of memory   : 0
% 0.54/0.75  # Backward-subsumed                    : 2
% 0.54/0.75  # Backward-rewritten                   : 113
% 0.54/0.75  # Generated clauses                    : 54684
% 0.54/0.75  # ...of the previous two non-trivial   : 44884
% 0.54/0.75  # Contextual simplify-reflections      : 2
% 0.54/0.75  # Paramodulations                      : 54513
% 0.54/0.75  # Factorizations                       : 168
% 0.54/0.75  # Equation resolutions                 : 3
% 0.54/0.75  # Propositional unsat checks           : 0
% 0.54/0.75  #    Propositional check models        : 0
% 0.54/0.75  #    Propositional check unsatisfiable : 0
% 0.54/0.75  #    Propositional clauses             : 0
% 0.54/0.75  #    Propositional clauses after purity: 0
% 0.54/0.75  #    Propositional unsat core size     : 0
% 0.54/0.75  #    Propositional preprocessing time  : 0.000
% 0.54/0.75  #    Propositional encoding time       : 0.000
% 0.54/0.75  #    Propositional solver time         : 0.000
% 0.54/0.75  #    Success case prop preproc time    : 0.000
% 0.54/0.75  #    Success case prop encoding time   : 0.000
% 0.54/0.75  #    Success case prop solver time     : 0.000
% 0.54/0.75  # Current number of processed clauses  : 238
% 0.54/0.75  #    Positive orientable unit clauses  : 63
% 0.54/0.75  #    Positive unorientable unit clauses: 8
% 0.54/0.75  #    Negative unit clauses             : 0
% 0.54/0.75  #    Non-unit-clauses                  : 167
% 0.54/0.75  # Current number of unprocessed clauses: 39983
% 0.54/0.75  # ...number of literals in the above   : 92930
% 0.54/0.75  # Current number of archived formulas  : 0
% 0.54/0.75  # Current number of archived clauses   : 126
% 0.54/0.75  # Clause-clause subsumption calls (NU) : 22965
% 0.54/0.75  # Rec. Clause-clause subsumption calls : 17501
% 0.54/0.75  # Non-unit clause-clause subsumptions  : 2164
% 0.54/0.75  # Unit Clause-clause subsumption calls : 336
% 0.54/0.75  # Rewrite failures with RHS unbound    : 0
% 0.54/0.75  # BW rewrite match attempts            : 883
% 0.54/0.75  # BW rewrite match successes           : 510
% 0.54/0.75  # Condensation attempts                : 0
% 0.54/0.75  # Condensation successes               : 0
% 0.54/0.75  # Termbank termtop insertions          : 608142
% 0.54/0.75  
% 0.54/0.75  # -------------------------------------------------
% 0.54/0.75  # User time                : 0.397 s
% 0.54/0.75  # System time              : 0.020 s
% 0.54/0.75  # Total time               : 0.417 s
% 0.54/0.75  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
