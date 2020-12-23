%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:41:55 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   34 (  53 expanded)
%              Number of clauses        :   19 (  23 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :    9
%              Number of atoms          :   74 ( 117 expanded)
%              Number of equality atoms :    6 (   9 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t114_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_xboole_0(X1,X4)
        & r1_xboole_0(X2,X4)
        & r1_xboole_0(X3,X4) )
     => r1_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_xboole_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t56_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_zfmisc_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t57_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X3,X2)
        & ~ r1_xboole_0(k2_tarski(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(c_0_7,plain,(
    ! [X5,X6,X7,X8] :
      ( ~ r1_xboole_0(X5,X8)
      | ~ r1_xboole_0(X6,X8)
      | ~ r1_xboole_0(X7,X8)
      | r1_xboole_0(k2_xboole_0(k2_xboole_0(X5,X6),X7),X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t114_xboole_1])])).

fof(c_0_8,plain,(
    ! [X9,X10,X11] : k2_xboole_0(k2_xboole_0(X9,X10),X11) = k2_xboole_0(X9,k2_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_9,plain,
    ( r1_xboole_0(k2_xboole_0(k2_xboole_0(X1,X3),X4),X2)
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X3,X2)
    | ~ r1_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X19,X20] :
      ( r2_hidden(X19,X20)
      | r1_xboole_0(k1_tarski(X19),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_zfmisc_1])])])).

fof(c_0_12,plain,(
    ! [X15,X16] : r1_tarski(X15,k2_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_13,plain,
    ( r1_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X4)
    | ~ r1_xboole_0(X3,X4)
    | ~ r1_xboole_0(X2,X4)
    | ~ r1_xboole_0(X1,X4) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X3,X2)
          & ~ r1_xboole_0(k2_tarski(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t57_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | ~ r1_xboole_0(X13,X14)
      | r1_xboole_0(X12,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k2_xboole_0(X3,k2_xboole_0(X4,k1_tarski(X1))),X2)
    | ~ r1_xboole_0(X4,X2)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_19,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk2_0)
    & ~ r2_hidden(esk3_0,esk2_0)
    & ~ r1_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_20,plain,(
    ! [X17,X18] : k2_tarski(X17,X18) = k2_xboole_0(k1_tarski(X17),k1_tarski(X18)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

cnf(c_0_21,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_10])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | r1_xboole_0(k2_xboole_0(X4,k2_xboole_0(k1_tarski(X1),k1_tarski(X3))),X2)
    | ~ r1_xboole_0(X4,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( ~ r1_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r1_xboole_0(k2_xboole_0(X1,X2),X3)
    | ~ r1_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X4)),X3) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | r2_hidden(X4,X2)
    | r1_xboole_0(k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X4),k1_tarski(X3))),X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk3_0)),esk2_0) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | r2_hidden(X4,X2)
    | r1_xboole_0(k2_xboole_0(k1_tarski(X4),k1_tarski(X1)),X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:33:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.20/0.37  # and selection function SelectDiffNegLit.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.024 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(t114_xboole_1, axiom, ![X1, X2, X3, X4]:(((r1_xboole_0(X1,X4)&r1_xboole_0(X2,X4))&r1_xboole_0(X3,X4))=>r1_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_xboole_1)).
% 0.20/0.37  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.20/0.37  fof(t56_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_zfmisc_1)).
% 0.20/0.37  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.20/0.37  fof(t57_zfmisc_1, conjecture, ![X1, X2, X3]:~(((~(r2_hidden(X1,X2))&~(r2_hidden(X3,X2)))&~(r1_xboole_0(k2_tarski(X1,X3),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 0.20/0.37  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.20/0.37  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.20/0.37  fof(c_0_7, plain, ![X5, X6, X7, X8]:(~r1_xboole_0(X5,X8)|~r1_xboole_0(X6,X8)|~r1_xboole_0(X7,X8)|r1_xboole_0(k2_xboole_0(k2_xboole_0(X5,X6),X7),X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t114_xboole_1])])).
% 0.20/0.37  fof(c_0_8, plain, ![X9, X10, X11]:k2_xboole_0(k2_xboole_0(X9,X10),X11)=k2_xboole_0(X9,k2_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.20/0.37  cnf(c_0_9, plain, (r1_xboole_0(k2_xboole_0(k2_xboole_0(X1,X3),X4),X2)|~r1_xboole_0(X1,X2)|~r1_xboole_0(X3,X2)|~r1_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.37  cnf(c_0_10, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.37  fof(c_0_11, plain, ![X19, X20]:(r2_hidden(X19,X20)|r1_xboole_0(k1_tarski(X19),X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_zfmisc_1])])])).
% 0.20/0.37  fof(c_0_12, plain, ![X15, X16]:r1_tarski(X15,k2_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.20/0.37  cnf(c_0_13, plain, (r1_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X4)|~r1_xboole_0(X3,X4)|~r1_xboole_0(X2,X4)|~r1_xboole_0(X1,X4)), inference(rw,[status(thm)],[c_0_9, c_0_10])).
% 0.20/0.37  cnf(c_0_14, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.37  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:~(((~(r2_hidden(X1,X2))&~(r2_hidden(X3,X2)))&~(r1_xboole_0(k2_tarski(X1,X3),X2))))), inference(assume_negation,[status(cth)],[t57_zfmisc_1])).
% 0.20/0.37  fof(c_0_16, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|~r1_xboole_0(X13,X14)|r1_xboole_0(X12,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.20/0.37  cnf(c_0_17, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.37  cnf(c_0_18, plain, (r2_hidden(X1,X2)|r1_xboole_0(k2_xboole_0(X3,k2_xboole_0(X4,k1_tarski(X1))),X2)|~r1_xboole_0(X4,X2)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.37  fof(c_0_19, negated_conjecture, ((~r2_hidden(esk1_0,esk2_0)&~r2_hidden(esk3_0,esk2_0))&~r1_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.20/0.37  fof(c_0_20, plain, ![X17, X18]:k2_tarski(X17,X18)=k2_xboole_0(k1_tarski(X17),k1_tarski(X18)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.20/0.37  cnf(c_0_21, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.37  cnf(c_0_22, plain, (r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X1,k2_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_17, c_0_10])).
% 0.20/0.37  cnf(c_0_23, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|r1_xboole_0(k2_xboole_0(X4,k2_xboole_0(k1_tarski(X1),k1_tarski(X3))),X2)|~r1_xboole_0(X4,X2)), inference(spm,[status(thm)],[c_0_18, c_0_14])).
% 0.20/0.37  cnf(c_0_24, negated_conjecture, (~r1_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.37  cnf(c_0_25, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.37  cnf(c_0_26, plain, (r1_xboole_0(k2_xboole_0(X1,X2),X3)|~r1_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X4)),X3)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.37  cnf(c_0_27, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|r2_hidden(X4,X2)|r1_xboole_0(k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X4),k1_tarski(X3))),X2)), inference(spm,[status(thm)],[c_0_23, c_0_14])).
% 0.20/0.37  cnf(c_0_28, negated_conjecture, (~r1_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk3_0)),esk2_0)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.37  cnf(c_0_29, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|r2_hidden(X4,X2)|r1_xboole_0(k2_xboole_0(k1_tarski(X4),k1_tarski(X1)),X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.37  cnf(c_0_30, negated_conjecture, (~r2_hidden(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.37  cnf(c_0_31, negated_conjecture, (~r2_hidden(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.37  cnf(c_0_32, negated_conjecture, (r2_hidden(X1,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31])).
% 0.20/0.37  cnf(c_0_33, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32])]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 34
% 0.20/0.37  # Proof object clause steps            : 19
% 0.20/0.37  # Proof object formula steps           : 15
% 0.20/0.37  # Proof object conjectures             : 9
% 0.20/0.37  # Proof object clause conjectures      : 6
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 9
% 0.20/0.37  # Proof object initial formulas used   : 7
% 0.20/0.37  # Proof object generating inferences   : 7
% 0.20/0.37  # Proof object simplifying inferences  : 6
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 7
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 9
% 0.20/0.37  # Removed in clause preprocessing      : 1
% 0.20/0.37  # Initial clauses in saturation        : 8
% 0.20/0.37  # Processed clauses                    : 37
% 0.20/0.37  # ...of these trivial                  : 2
% 0.20/0.37  # ...subsumed                          : 7
% 0.20/0.37  # ...remaining for further processing  : 28
% 0.20/0.37  # Other redundant clauses eliminated   : 0
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 2
% 0.20/0.37  # Generated clauses                    : 41
% 0.20/0.37  # ...of the previous two non-trivial   : 40
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 41
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 0
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 18
% 0.20/0.37  #    Positive orientable unit clauses  : 5
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 1
% 0.20/0.37  #    Non-unit-clauses                  : 12
% 0.20/0.37  # Current number of unprocessed clauses: 19
% 0.20/0.37  # ...number of literals in the above   : 59
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 11
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 56
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 39
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 7
% 0.20/0.37  # Unit Clause-clause subsumption calls : 5
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 2
% 0.20/0.37  # BW rewrite match successes           : 2
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 1349
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.023 s
% 0.20/0.37  # System time              : 0.006 s
% 0.20/0.37  # Total time               : 0.029 s
% 0.20/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
