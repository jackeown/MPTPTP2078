%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:30 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 126 expanded)
%              Number of clauses        :   23 (  55 expanded)
%              Number of leaves         :    7 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :   97 ( 310 expanded)
%              Number of equality atoms :   17 (  38 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(l45_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_tarski(X2,X3))
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(k2_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,X3)
          & r2_hidden(X2,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t38_zfmisc_1])).

fof(c_0_8,negated_conjecture,
    ( ( ~ r1_tarski(k2_tarski(esk1_0,esk2_0),esk3_0)
      | ~ r2_hidden(esk1_0,esk3_0)
      | ~ r2_hidden(esk2_0,esk3_0) )
    & ( r2_hidden(esk1_0,esk3_0)
      | r1_tarski(k2_tarski(esk1_0,esk2_0),esk3_0) )
    & ( r2_hidden(esk2_0,esk3_0)
      | r1_tarski(k2_tarski(esk1_0,esk2_0),esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

fof(c_0_9,plain,(
    ! [X13,X14] : k2_tarski(X13,X14) = k2_xboole_0(k1_tarski(X13),k1_tarski(X14)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_10,plain,(
    ! [X4,X5,X6] :
      ( ~ r1_tarski(k2_xboole_0(X4,X5),X6)
      | r1_tarski(X4,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0)
    | r1_tarski(k2_tarski(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X15,X16] :
      ( ( ~ r1_tarski(k1_tarski(X15),X16)
        | r2_hidden(X15,X16) )
      & ( ~ r2_hidden(X15,X16)
        | r1_tarski(k1_tarski(X15),X16) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_14,negated_conjecture,
    ( ~ r1_tarski(k2_tarski(esk1_0,esk2_0),esk3_0)
    | ~ r2_hidden(esk1_0,esk3_0)
    | ~ r2_hidden(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0)
    | r1_tarski(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),esk3_0) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk3_0)
    | ~ r2_hidden(esk2_0,esk3_0)
    | ~ r1_tarski(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),esk3_0) ),
    inference(rw,[status(thm)],[c_0_14,c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

fof(c_0_20,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,X11)
      | ~ r1_tarski(X12,X11)
      | r1_tarski(k2_xboole_0(X10,X12),X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_21,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | r1_tarski(k2_tarski(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0)
    | ~ r1_tarski(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19])])).

cnf(c_0_24,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(k1_tarski(esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_19])).

fof(c_0_26,plain,(
    ! [X17,X18,X19] :
      ( ( ~ r1_tarski(X17,k2_tarski(X18,X19))
        | X17 = k1_xboole_0
        | X17 = k1_tarski(X18)
        | X17 = k1_tarski(X19)
        | X17 = k2_tarski(X18,X19) )
      & ( X17 != k1_xboole_0
        | r1_tarski(X17,k2_tarski(X18,X19)) )
      & ( X17 != k1_tarski(X18)
        | r1_tarski(X17,k2_tarski(X18,X19)) )
      & ( X17 != k1_tarski(X19)
        | r1_tarski(X17,k2_tarski(X18,X19)) )
      & ( X17 != k2_tarski(X18,X19)
        | r1_tarski(X17,k2_tarski(X18,X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).

fof(c_0_27,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X8,X9)
      | r1_tarski(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | r1_tarski(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),esk3_0) ),
    inference(rw,[status(thm)],[c_0_22,c_0_12])).

cnf(c_0_29,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])]),c_0_21])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,k2_tarski(X3,X2))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),esk3_0) ),
    inference(sr,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k2_xboole_0(k1_tarski(X3),k1_tarski(X2)))
    | X1 != k1_tarski(X2) ),
    inference(rw,[status(thm)],[c_0_30,c_0_12])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,plain,
    ( r1_tarski(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_tarski(X1))) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_tarski(k1_tarski(esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_17])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:59:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.19/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.029 s
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t38_zfmisc_1, conjecture, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.19/0.37  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.19/0.37  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.19/0.37  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.19/0.37  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.19/0.37  fof(l45_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_tarski(X2,X3))<=>~((((X1!=k1_xboole_0&X1!=k1_tarski(X2))&X1!=k1_tarski(X3))&X1!=k2_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 0.19/0.37  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.19/0.37  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3)))), inference(assume_negation,[status(cth)],[t38_zfmisc_1])).
% 0.19/0.37  fof(c_0_8, negated_conjecture, ((~r1_tarski(k2_tarski(esk1_0,esk2_0),esk3_0)|(~r2_hidden(esk1_0,esk3_0)|~r2_hidden(esk2_0,esk3_0)))&((r2_hidden(esk1_0,esk3_0)|r1_tarski(k2_tarski(esk1_0,esk2_0),esk3_0))&(r2_hidden(esk2_0,esk3_0)|r1_tarski(k2_tarski(esk1_0,esk2_0),esk3_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).
% 0.19/0.37  fof(c_0_9, plain, ![X13, X14]:k2_tarski(X13,X14)=k2_xboole_0(k1_tarski(X13),k1_tarski(X14)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.19/0.37  fof(c_0_10, plain, ![X4, X5, X6]:(~r1_tarski(k2_xboole_0(X4,X5),X6)|r1_tarski(X4,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.19/0.37  cnf(c_0_11, negated_conjecture, (r2_hidden(esk1_0,esk3_0)|r1_tarski(k2_tarski(esk1_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_12, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  fof(c_0_13, plain, ![X15, X16]:((~r1_tarski(k1_tarski(X15),X16)|r2_hidden(X15,X16))&(~r2_hidden(X15,X16)|r1_tarski(k1_tarski(X15),X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.19/0.37  cnf(c_0_14, negated_conjecture, (~r1_tarski(k2_tarski(esk1_0,esk2_0),esk3_0)|~r2_hidden(esk1_0,esk3_0)|~r2_hidden(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_15, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_16, negated_conjecture, (r2_hidden(esk1_0,esk3_0)|r1_tarski(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),esk3_0)), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.19/0.37  cnf(c_0_17, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (~r2_hidden(esk1_0,esk3_0)|~r2_hidden(esk2_0,esk3_0)|~r1_tarski(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),esk3_0)), inference(rw,[status(thm)],[c_0_14, c_0_12])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (r2_hidden(esk1_0,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 0.19/0.37  fof(c_0_20, plain, ![X10, X11, X12]:(~r1_tarski(X10,X11)|~r1_tarski(X12,X11)|r1_tarski(k2_xboole_0(X10,X12),X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.19/0.37  cnf(c_0_21, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (r2_hidden(esk2_0,esk3_0)|r1_tarski(k2_tarski(esk1_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (~r2_hidden(esk2_0,esk3_0)|~r1_tarski(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19])])).
% 0.19/0.37  cnf(c_0_24, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.37  cnf(c_0_25, negated_conjecture, (r1_tarski(k1_tarski(esk1_0),esk3_0)), inference(spm,[status(thm)],[c_0_21, c_0_19])).
% 0.19/0.37  fof(c_0_26, plain, ![X17, X18, X19]:((~r1_tarski(X17,k2_tarski(X18,X19))|(X17=k1_xboole_0|X17=k1_tarski(X18)|X17=k1_tarski(X19)|X17=k2_tarski(X18,X19)))&((((X17!=k1_xboole_0|r1_tarski(X17,k2_tarski(X18,X19)))&(X17!=k1_tarski(X18)|r1_tarski(X17,k2_tarski(X18,X19))))&(X17!=k1_tarski(X19)|r1_tarski(X17,k2_tarski(X18,X19))))&(X17!=k2_tarski(X18,X19)|r1_tarski(X17,k2_tarski(X18,X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).
% 0.19/0.37  fof(c_0_27, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|~r1_tarski(X8,X9)|r1_tarski(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.19/0.37  cnf(c_0_28, negated_conjecture, (r2_hidden(esk2_0,esk3_0)|r1_tarski(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),esk3_0)), inference(rw,[status(thm)],[c_0_22, c_0_12])).
% 0.19/0.37  cnf(c_0_29, negated_conjecture, (~r2_hidden(esk2_0,esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])]), c_0_21])).
% 0.19/0.37  cnf(c_0_30, plain, (r1_tarski(X1,k2_tarski(X3,X2))|X1!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.37  cnf(c_0_31, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.37  cnf(c_0_32, negated_conjecture, (r1_tarski(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),esk3_0)), inference(sr,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.37  cnf(c_0_33, plain, (r1_tarski(X1,k2_xboole_0(k1_tarski(X3),k1_tarski(X2)))|X1!=k1_tarski(X2)), inference(rw,[status(thm)],[c_0_30, c_0_12])).
% 0.19/0.37  cnf(c_0_34, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X1,k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.37  cnf(c_0_35, plain, (r1_tarski(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_tarski(X1)))), inference(er,[status(thm)],[c_0_33])).
% 0.19/0.37  cnf(c_0_36, negated_conjecture, (~r1_tarski(k1_tarski(esk2_0),esk3_0)), inference(spm,[status(thm)],[c_0_29, c_0_17])).
% 0.19/0.37  cnf(c_0_37, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 38
% 0.19/0.37  # Proof object clause steps            : 23
% 0.19/0.37  # Proof object formula steps           : 15
% 0.19/0.37  # Proof object conjectures             : 17
% 0.19/0.37  # Proof object clause conjectures      : 14
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 10
% 0.19/0.37  # Proof object initial formulas used   : 7
% 0.19/0.37  # Proof object generating inferences   : 6
% 0.19/0.37  # Proof object simplifying inferences  : 13
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 8
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 16
% 0.19/0.37  # Removed in clause preprocessing      : 1
% 0.19/0.37  # Initial clauses in saturation        : 15
% 0.19/0.37  # Processed clauses                    : 31
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 3
% 0.19/0.37  # ...remaining for further processing  : 28
% 0.19/0.37  # Other redundant clauses eliminated   : 3
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 3
% 0.19/0.37  # Generated clauses                    : 49
% 0.19/0.37  # ...of the previous two non-trivial   : 33
% 0.19/0.37  # Contextual simplify-reflections      : 2
% 0.19/0.37  # Paramodulations                      : 45
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 3
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 21
% 0.19/0.37  #    Positive orientable unit clauses  : 6
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 2
% 0.19/0.37  #    Non-unit-clauses                  : 13
% 0.19/0.37  # Current number of unprocessed clauses: 15
% 0.19/0.37  # ...number of literals in the above   : 48
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 5
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 28
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 27
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 4
% 0.19/0.37  # Unit Clause-clause subsumption calls : 4
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 4
% 0.19/0.37  # BW rewrite match successes           : 3
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 1576
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.032 s
% 0.19/0.37  # System time              : 0.002 s
% 0.19/0.37  # Total time               : 0.034 s
% 0.19/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
