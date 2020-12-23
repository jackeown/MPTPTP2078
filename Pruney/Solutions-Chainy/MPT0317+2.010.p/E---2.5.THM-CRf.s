%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:45 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 216 expanded)
%              Number of clauses        :   28 (  92 expanded)
%              Number of leaves         :    7 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :  110 ( 505 expanded)
%              Number of equality atoms :   51 ( 229 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t129_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X4)))
    <=> ( r2_hidden(X1,X3)
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(t76_enumset1,axiom,(
    ! [X1] : k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X4)))
      <=> ( r2_hidden(X1,X3)
          & X2 = X4 ) ) ),
    inference(assume_negation,[status(cth)],[t129_zfmisc_1])).

fof(c_0_8,negated_conjecture,
    ( ( ~ r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,k1_tarski(esk5_0)))
      | ~ r2_hidden(esk2_0,esk4_0)
      | esk3_0 != esk5_0 )
    & ( r2_hidden(esk2_0,esk4_0)
      | r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,k1_tarski(esk5_0))) )
    & ( esk3_0 = esk5_0
      | r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,k1_tarski(esk5_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

fof(c_0_9,plain,(
    ! [X21] : k1_enumset1(X21,X21,X21) = k1_tarski(X21) ),
    inference(variable_rename,[status(thm)],[t76_enumset1])).

fof(c_0_10,plain,(
    ! [X14,X15,X16] : k2_enumset1(X14,X14,X15,X16) = k1_enumset1(X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_11,plain,(
    ! [X17,X18,X19,X20] : k3_enumset1(X17,X17,X18,X19,X20) = k2_enumset1(X17,X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,k1_tarski(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X24,X25,X26,X27] :
      ( ( r2_hidden(X24,X26)
        | ~ r2_hidden(k4_tarski(X24,X25),k2_zfmisc_1(X26,X27)) )
      & ( r2_hidden(X25,X27)
        | ~ r2_hidden(k4_tarski(X24,X25),k2_zfmisc_1(X26,X27)) )
      & ( ~ r2_hidden(X24,X26)
        | ~ r2_hidden(X25,X27)
        | r2_hidden(k4_tarski(X24,X25),k2_zfmisc_1(X26,X27)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

fof(c_0_17,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | X8 = X5
        | X8 = X6
        | X7 != k2_tarski(X5,X6) )
      & ( X9 != X5
        | r2_hidden(X9,X7)
        | X7 != k2_tarski(X5,X6) )
      & ( X9 != X6
        | r2_hidden(X9,X7)
        | X7 != k2_tarski(X5,X6) )
      & ( esk1_3(X10,X11,X12) != X10
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_tarski(X10,X11) )
      & ( esk1_3(X10,X11,X12) != X11
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_tarski(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | esk1_3(X10,X11,X12) = X10
        | esk1_3(X10,X11,X12) = X11
        | X12 = k2_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_18,plain,(
    ! [X22,X23] : k2_enumset1(X22,X22,X22,X23) = k2_tarski(X22,X23) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

cnf(c_0_19,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,k1_tarski(esk5_0)))
    | ~ r2_hidden(esk2_0,esk4_0)
    | esk3_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( esk5_0 != esk3_0
    | ~ r2_hidden(esk2_0,esk4_0)
    | ~ r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_13]),c_0_14]),c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0) ),
    inference(csr,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( esk3_0 = esk5_0
    | r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,k1_tarski(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X4,X4,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( esk3_0 != esk5_0
    | ~ r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25])])).

cnf(c_0_30,negated_conjecture,
    ( esk5_0 = esk3_0
    | r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_13]),c_0_14]),c_0_15])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_0,X1),k2_zfmisc_1(esk4_0,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_25])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_28])])).

cnf(c_0_33,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))
    | ~ r2_hidden(k4_tarski(esk2_0,esk5_0),k2_zfmisc_1(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_0,X1),k2_zfmisc_1(esk4_0,k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_23]),c_0_15])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35])])).

cnf(c_0_39,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k3_enumset1(X3,X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk3_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( esk3_0 != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_38])])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:28:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.19/0.39  # and selection function SelectNegativeLiterals.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.026 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t129_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X4)))<=>(r2_hidden(X1,X3)&X2=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 0.19/0.39  fof(t76_enumset1, axiom, ![X1]:k1_enumset1(X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_enumset1)).
% 0.19/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.39  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.19/0.39  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.19/0.39  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 0.19/0.39  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X4)))<=>(r2_hidden(X1,X3)&X2=X4))), inference(assume_negation,[status(cth)],[t129_zfmisc_1])).
% 0.19/0.39  fof(c_0_8, negated_conjecture, ((~r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,k1_tarski(esk5_0)))|(~r2_hidden(esk2_0,esk4_0)|esk3_0!=esk5_0))&((r2_hidden(esk2_0,esk4_0)|r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,k1_tarski(esk5_0))))&(esk3_0=esk5_0|r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,k1_tarski(esk5_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).
% 0.19/0.39  fof(c_0_9, plain, ![X21]:k1_enumset1(X21,X21,X21)=k1_tarski(X21), inference(variable_rename,[status(thm)],[t76_enumset1])).
% 0.19/0.39  fof(c_0_10, plain, ![X14, X15, X16]:k2_enumset1(X14,X14,X15,X16)=k1_enumset1(X14,X15,X16), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.39  fof(c_0_11, plain, ![X17, X18, X19, X20]:k3_enumset1(X17,X17,X18,X19,X20)=k2_enumset1(X17,X18,X19,X20), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.39  cnf(c_0_12, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,k1_tarski(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_13, plain, (k1_enumset1(X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_14, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  cnf(c_0_15, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  fof(c_0_16, plain, ![X24, X25, X26, X27]:(((r2_hidden(X24,X26)|~r2_hidden(k4_tarski(X24,X25),k2_zfmisc_1(X26,X27)))&(r2_hidden(X25,X27)|~r2_hidden(k4_tarski(X24,X25),k2_zfmisc_1(X26,X27))))&(~r2_hidden(X24,X26)|~r2_hidden(X25,X27)|r2_hidden(k4_tarski(X24,X25),k2_zfmisc_1(X26,X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.19/0.39  fof(c_0_17, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(X8=X5|X8=X6)|X7!=k2_tarski(X5,X6))&((X9!=X5|r2_hidden(X9,X7)|X7!=k2_tarski(X5,X6))&(X9!=X6|r2_hidden(X9,X7)|X7!=k2_tarski(X5,X6))))&(((esk1_3(X10,X11,X12)!=X10|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_tarski(X10,X11))&(esk1_3(X10,X11,X12)!=X11|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_tarski(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(esk1_3(X10,X11,X12)=X10|esk1_3(X10,X11,X12)=X11)|X12=k2_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.19/0.39  fof(c_0_18, plain, ![X22, X23]:k2_enumset1(X22,X22,X22,X23)=k2_tarski(X22,X23), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.19/0.39  cnf(c_0_19, negated_conjecture, (~r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,k1_tarski(esk5_0)))|~r2_hidden(esk2_0,esk4_0)|esk3_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_20, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_13]), c_0_14]), c_0_15])).
% 0.19/0.39  cnf(c_0_21, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.39  cnf(c_0_22, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_23, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_24, negated_conjecture, (esk5_0!=esk3_0|~r2_hidden(esk2_0,esk4_0)|~r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_13]), c_0_14]), c_0_15])).
% 0.19/0.39  cnf(c_0_25, negated_conjecture, (r2_hidden(esk2_0,esk4_0)), inference(csr,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.39  cnf(c_0_26, negated_conjecture, (esk3_0=esk5_0|r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,k1_tarski(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_27, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.39  cnf(c_0_28, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X4,X4,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_15])).
% 0.19/0.39  cnf(c_0_29, negated_conjecture, (esk3_0!=esk5_0|~r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25])])).
% 0.19/0.39  cnf(c_0_30, negated_conjecture, (esk5_0=esk3_0|r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_13]), c_0_14]), c_0_15])).
% 0.19/0.39  cnf(c_0_31, negated_conjecture, (r2_hidden(k4_tarski(esk2_0,X1),k2_zfmisc_1(esk4_0,X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_27, c_0_25])).
% 0.19/0.39  cnf(c_0_32, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_28])])).
% 0.19/0.39  cnf(c_0_33, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_34, negated_conjecture, (r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))|~r2_hidden(k4_tarski(esk2_0,esk5_0),k2_zfmisc_1(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.39  cnf(c_0_35, negated_conjecture, (r2_hidden(k4_tarski(esk2_0,X1),k2_zfmisc_1(esk4_0,k3_enumset1(X2,X2,X2,X2,X1)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.39  cnf(c_0_36, plain, (X1=X4|X1=X3|X2!=k3_enumset1(X3,X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_23]), c_0_15])).
% 0.19/0.39  cnf(c_0_37, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.39  cnf(c_0_38, negated_conjecture, (r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35])])).
% 0.19/0.39  cnf(c_0_39, plain, (X1=X2|X1=X3|~r2_hidden(X1,k3_enumset1(X3,X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_36])).
% 0.19/0.39  cnf(c_0_40, negated_conjecture, (r2_hidden(esk3_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.39  cnf(c_0_41, negated_conjecture, (esk3_0!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_38])])).
% 0.19/0.39  cnf(c_0_42, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 43
% 0.19/0.39  # Proof object clause steps            : 28
% 0.19/0.39  # Proof object formula steps           : 15
% 0.19/0.39  # Proof object conjectures             : 18
% 0.19/0.39  # Proof object clause conjectures      : 15
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 12
% 0.19/0.39  # Proof object initial formulas used   : 7
% 0.19/0.39  # Proof object generating inferences   : 5
% 0.19/0.39  # Proof object simplifying inferences  : 24
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 7
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 16
% 0.19/0.39  # Removed in clause preprocessing      : 4
% 0.19/0.39  # Initial clauses in saturation        : 12
% 0.19/0.39  # Processed clauses                    : 86
% 0.19/0.39  # ...of these trivial                  : 0
% 0.19/0.39  # ...subsumed                          : 4
% 0.19/0.39  # ...remaining for further processing  : 82
% 0.19/0.39  # Other redundant clauses eliminated   : 19
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 0
% 0.19/0.39  # Backward-rewritten                   : 4
% 0.19/0.39  # Generated clauses                    : 515
% 0.19/0.39  # ...of the previous two non-trivial   : 443
% 0.19/0.39  # Contextual simplify-reflections      : 1
% 0.19/0.39  # Paramodulations                      : 492
% 0.19/0.39  # Factorizations                       : 6
% 0.19/0.39  # Equation resolutions                 : 19
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 63
% 0.19/0.39  #    Positive orientable unit clauses  : 27
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 1
% 0.19/0.39  #    Non-unit-clauses                  : 35
% 0.19/0.39  # Current number of unprocessed clauses: 370
% 0.19/0.39  # ...number of literals in the above   : 1008
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 20
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 1077
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 240
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 5
% 0.19/0.39  # Unit Clause-clause subsumption calls : 96
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 77
% 0.19/0.39  # BW rewrite match successes           : 3
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 17403
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.036 s
% 0.19/0.39  # System time              : 0.008 s
% 0.19/0.39  # Total time               : 0.044 s
% 0.19/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
