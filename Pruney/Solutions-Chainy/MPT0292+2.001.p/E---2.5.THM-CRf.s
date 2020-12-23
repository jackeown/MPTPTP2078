%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:20 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   47 (  88 expanded)
%              Number of clauses        :   28 (  43 expanded)
%              Number of leaves         :    9 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :   89 ( 171 expanded)
%              Number of equality atoms :   31 (  64 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t94_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X3,X2) )
     => r1_tarski(k3_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t99_zfmisc_1,conjecture,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(c_0_9,plain,(
    ! [X21,X22] : k3_tarski(k2_tarski(X21,X22)) = k2_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X10,X11] : k1_enumset1(X10,X10,X11) = k2_tarski(X10,X11) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_11,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X4,X5)
      | k2_xboole_0(X4,X5) = X5 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_12,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X8,X9] : k2_tarski(X8,X9) = k2_tarski(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_15,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X12,X13,X14,X15,X16,X17] :
      ( ( ~ r2_hidden(X14,X13)
        | r1_tarski(X14,X12)
        | X13 != k1_zfmisc_1(X12) )
      & ( ~ r1_tarski(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k1_zfmisc_1(X12) )
      & ( ~ r2_hidden(esk1_2(X16,X17),X17)
        | ~ r1_tarski(esk1_2(X16,X17),X16)
        | X17 = k1_zfmisc_1(X16) )
      & ( r2_hidden(esk1_2(X16,X17),X17)
        | r1_tarski(esk1_2(X16,X17),X16)
        | X17 = k1_zfmisc_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_19,plain,(
    ! [X23,X24] :
      ( ( r2_hidden(esk2_2(X23,X24),X23)
        | r1_tarski(k3_tarski(X23),X24) )
      & ( ~ r1_tarski(esk2_2(X23,X24),X24)
        | r1_tarski(k3_tarski(X23),X24) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).

fof(c_0_20,plain,(
    ! [X19,X20] :
      ( ~ r2_hidden(X19,X20)
      | r1_tarski(X19,k3_tarski(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_21,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_13]),c_0_13])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(k3_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r2_hidden(esk2_2(X1,k3_tarski(X2)),X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_26])).

cnf(c_0_31,plain,
    ( r1_tarski(esk2_2(k1_zfmisc_1(X1),X2),X1)
    | r1_tarski(k3_tarski(k1_zfmisc_1(X1)),X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_28])).

fof(c_0_33,plain,(
    ! [X6,X7] : r1_tarski(k3_xboole_0(X6,X7),X6) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_34,negated_conjecture,(
    ~ ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t99_zfmisc_1])).

cnf(c_0_35,plain,
    ( X1 = k3_tarski(X2)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(k3_tarski(X2),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_25])).

cnf(c_0_36,plain,
    ( r1_tarski(k3_tarski(k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_31])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_21])).

cnf(c_0_39,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_40,negated_conjecture,(
    k3_tarski(k1_zfmisc_1(esk3_0)) != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_34])])])).

cnf(c_0_41,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1
    | ~ r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( k3_tarski(k1_zfmisc_1(esk3_0)) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_45,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:27:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.12/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.37  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.12/0.37  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.12/0.37  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.12/0.37  fof(t94_zfmisc_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X3,X2))=>r1_tarski(k3_tarski(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 0.12/0.37  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.12/0.37  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.12/0.37  fof(t99_zfmisc_1, conjecture, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.12/0.37  fof(c_0_9, plain, ![X21, X22]:k3_tarski(k2_tarski(X21,X22))=k2_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.12/0.37  fof(c_0_10, plain, ![X10, X11]:k1_enumset1(X10,X10,X11)=k2_tarski(X10,X11), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.37  fof(c_0_11, plain, ![X4, X5]:(~r1_tarski(X4,X5)|k2_xboole_0(X4,X5)=X5), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.12/0.37  cnf(c_0_12, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_13, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  fof(c_0_14, plain, ![X8, X9]:k2_tarski(X8,X9)=k2_tarski(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.12/0.37  cnf(c_0_15, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_16, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.12/0.37  cnf(c_0_17, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.37  fof(c_0_18, plain, ![X12, X13, X14, X15, X16, X17]:(((~r2_hidden(X14,X13)|r1_tarski(X14,X12)|X13!=k1_zfmisc_1(X12))&(~r1_tarski(X15,X12)|r2_hidden(X15,X13)|X13!=k1_zfmisc_1(X12)))&((~r2_hidden(esk1_2(X16,X17),X17)|~r1_tarski(esk1_2(X16,X17),X16)|X17=k1_zfmisc_1(X16))&(r2_hidden(esk1_2(X16,X17),X17)|r1_tarski(esk1_2(X16,X17),X16)|X17=k1_zfmisc_1(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.12/0.37  fof(c_0_19, plain, ![X23, X24]:((r2_hidden(esk2_2(X23,X24),X23)|r1_tarski(k3_tarski(X23),X24))&(~r1_tarski(esk2_2(X23,X24),X24)|r1_tarski(k3_tarski(X23),X24))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).
% 0.12/0.37  fof(c_0_20, plain, ![X19, X20]:(~r2_hidden(X19,X20)|r1_tarski(X19,k3_tarski(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.12/0.37  cnf(c_0_21, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.12/0.37  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_13]), c_0_13])).
% 0.12/0.37  cnf(c_0_23, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.37  cnf(c_0_24, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.37  cnf(c_0_25, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_26, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.12/0.37  cnf(c_0_27, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_23])).
% 0.12/0.37  cnf(c_0_28, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(k3_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.37  cnf(c_0_29, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r2_hidden(esk2_2(X1,k3_tarski(X2)),X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.12/0.37  cnf(c_0_30, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_21, c_0_26])).
% 0.12/0.37  cnf(c_0_31, plain, (r1_tarski(esk2_2(k1_zfmisc_1(X1),X2),X1)|r1_tarski(k3_tarski(k1_zfmisc_1(X1)),X2)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.12/0.37  cnf(c_0_32, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X1))), inference(spm,[status(thm)],[c_0_29, c_0_28])).
% 0.12/0.37  fof(c_0_33, plain, ![X6, X7]:r1_tarski(k3_xboole_0(X6,X7),X6), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.12/0.37  fof(c_0_34, negated_conjecture, ~(![X1]:k3_tarski(k1_zfmisc_1(X1))=X1), inference(assume_negation,[status(cth)],[t99_zfmisc_1])).
% 0.12/0.37  cnf(c_0_35, plain, (X1=k3_tarski(X2)|~r2_hidden(X1,X2)|~r1_tarski(k3_tarski(X2),X1)), inference(spm,[status(thm)],[c_0_30, c_0_25])).
% 0.12/0.37  cnf(c_0_36, plain, (r1_tarski(k3_tarski(k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_24, c_0_31])).
% 0.12/0.37  cnf(c_0_37, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.37  cnf(c_0_38, plain, (r1_tarski(X1,X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_32, c_0_21])).
% 0.12/0.37  cnf(c_0_39, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.37  fof(c_0_40, negated_conjecture, k3_tarski(k1_zfmisc_1(esk3_0))!=esk3_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_34])])])).
% 0.12/0.37  cnf(c_0_41, plain, (k3_tarski(k1_zfmisc_1(X1))=X1|~r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.12/0.37  cnf(c_0_42, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_37])).
% 0.12/0.37  cnf(c_0_43, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.12/0.37  cnf(c_0_44, negated_conjecture, (k3_tarski(k1_zfmisc_1(esk3_0))!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.12/0.37  cnf(c_0_45, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])])).
% 0.12/0.37  cnf(c_0_46, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 47
% 0.12/0.37  # Proof object clause steps            : 28
% 0.12/0.37  # Proof object formula steps           : 19
% 0.12/0.37  # Proof object conjectures             : 5
% 0.12/0.37  # Proof object clause conjectures      : 2
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 11
% 0.12/0.37  # Proof object initial formulas used   : 9
% 0.12/0.37  # Proof object generating inferences   : 11
% 0.12/0.37  # Proof object simplifying inferences  : 10
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 9
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 13
% 0.12/0.37  # Removed in clause preprocessing      : 2
% 0.12/0.37  # Initial clauses in saturation        : 11
% 0.12/0.37  # Processed clauses                    : 54
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 7
% 0.12/0.37  # ...remaining for further processing  : 47
% 0.12/0.37  # Other redundant clauses eliminated   : 2
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 13
% 0.12/0.37  # Generated clauses                    : 72
% 0.12/0.37  # ...of the previous two non-trivial   : 69
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 70
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 2
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 21
% 0.12/0.37  #    Positive orientable unit clauses  : 3
% 0.12/0.37  #    Positive unorientable unit clauses: 1
% 0.12/0.37  #    Negative unit clauses             : 0
% 0.12/0.37  #    Non-unit-clauses                  : 17
% 0.12/0.37  # Current number of unprocessed clauses: 27
% 0.12/0.37  # ...number of literals in the above   : 89
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 26
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 46
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 46
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 7
% 0.12/0.37  # Unit Clause-clause subsumption calls : 10
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 34
% 0.12/0.37  # BW rewrite match successes           : 14
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 1879
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.031 s
% 0.12/0.37  # System time              : 0.002 s
% 0.12/0.37  # Total time               : 0.033 s
% 0.12/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
