%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:04 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   28 (  76 expanded)
%              Number of clauses        :   19 (  33 expanded)
%              Number of leaves         :    4 (  19 expanded)
%              Depth                    :   13
%              Number of atoms          :   71 ( 197 expanded)
%              Number of equality atoms :    3 (  24 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ~ r1_xboole_0(k4_zfmisc_1(X1,X2,X3,X4),k4_zfmisc_1(X5,X6,X7,X8))
     => ( ~ r1_xboole_0(X1,X5)
        & ~ r1_xboole_0(X2,X6)
        & ~ r1_xboole_0(X3,X7)
        & ~ r1_xboole_0(X4,X8) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_mcart_1)).

fof(t54_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) = k4_zfmisc_1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_mcart_1)).

fof(t52_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ~ r1_xboole_0(k3_zfmisc_1(X1,X2,X3),k3_zfmisc_1(X4,X5,X6))
     => ( ~ r1_xboole_0(X1,X4)
        & ~ r1_xboole_0(X2,X5)
        & ~ r1_xboole_0(X3,X6) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_mcart_1)).

fof(t127_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_xboole_0(X1,X2)
        | r1_xboole_0(X3,X4) )
     => r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] :
        ( ~ r1_xboole_0(k4_zfmisc_1(X1,X2,X3,X4),k4_zfmisc_1(X5,X6,X7,X8))
       => ( ~ r1_xboole_0(X1,X5)
          & ~ r1_xboole_0(X2,X6)
          & ~ r1_xboole_0(X3,X7)
          & ~ r1_xboole_0(X4,X8) ) ) ),
    inference(assume_negation,[status(cth)],[t64_mcart_1])).

fof(c_0_5,negated_conjecture,
    ( ~ r1_xboole_0(k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))
    & ( r1_xboole_0(esk1_0,esk5_0)
      | r1_xboole_0(esk2_0,esk6_0)
      | r1_xboole_0(esk3_0,esk7_0)
      | r1_xboole_0(esk4_0,esk8_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).

fof(c_0_6,plain,(
    ! [X19,X20,X21,X22] : k3_zfmisc_1(k2_zfmisc_1(X19,X20),X21,X22) = k4_zfmisc_1(X19,X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t54_mcart_1])).

fof(c_0_7,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( ~ r1_xboole_0(X13,X16)
        | r1_xboole_0(k3_zfmisc_1(X13,X14,X15),k3_zfmisc_1(X16,X17,X18)) )
      & ( ~ r1_xboole_0(X14,X17)
        | r1_xboole_0(k3_zfmisc_1(X13,X14,X15),k3_zfmisc_1(X16,X17,X18)) )
      & ( ~ r1_xboole_0(X15,X18)
        | r1_xboole_0(k3_zfmisc_1(X13,X14,X15),k3_zfmisc_1(X16,X17,X18)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_mcart_1])])])])).

cnf(c_0_8,negated_conjecture,
    ( ~ r1_xboole_0(k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) = k4_zfmisc_1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r1_xboole_0(k3_zfmisc_1(X3,X4,X1),k3_zfmisc_1(X5,X6,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk5_0)
    | r1_xboole_0(esk2_0,esk6_0)
    | r1_xboole_0(esk3_0,esk7_0)
    | r1_xboole_0(esk4_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( ~ r1_xboole_0(k3_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0,esk4_0),k3_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_8,c_0_9]),c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( r1_xboole_0(k3_zfmisc_1(X1,X2,esk4_0),k3_zfmisc_1(X3,X4,esk8_0))
    | r1_xboole_0(esk3_0,esk7_0)
    | r1_xboole_0(esk2_0,esk6_0)
    | r1_xboole_0(esk1_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,plain,
    ( r1_xboole_0(k3_zfmisc_1(X3,X1,X4),k3_zfmisc_1(X5,X2,X6))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk5_0)
    | r1_xboole_0(esk2_0,esk6_0)
    | r1_xboole_0(esk3_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_16,plain,(
    ! [X9,X10,X11,X12] :
      ( ( ~ r1_xboole_0(X9,X10)
        | r1_xboole_0(k2_zfmisc_1(X9,X11),k2_zfmisc_1(X10,X12)) )
      & ( ~ r1_xboole_0(X11,X12)
        | r1_xboole_0(k2_zfmisc_1(X9,X11),k2_zfmisc_1(X10,X12)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).

cnf(c_0_17,negated_conjecture,
    ( r1_xboole_0(k3_zfmisc_1(X1,esk3_0,X2),k3_zfmisc_1(X3,esk7_0,X4))
    | r1_xboole_0(esk2_0,esk6_0)
    | r1_xboole_0(esk1_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,plain,
    ( r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk5_0)
    | r1_xboole_0(esk2_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_17])).

cnf(c_0_20,plain,
    ( r1_xboole_0(k3_zfmisc_1(X1,X3,X4),k3_zfmisc_1(X2,X5,X6))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,negated_conjecture,
    ( r1_xboole_0(k2_zfmisc_1(X1,esk2_0),k2_zfmisc_1(X2,esk6_0))
    | r1_xboole_0(esk1_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( r1_xboole_0(k3_zfmisc_1(k2_zfmisc_1(X1,esk2_0),X2,X3),k3_zfmisc_1(k2_zfmisc_1(X4,esk6_0),X5,X6))
    | r1_xboole_0(esk1_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_23,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( r1_xboole_0(k2_zfmisc_1(esk1_0,X1),k2_zfmisc_1(esk5_0,X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_26,negated_conjecture,
    ( r1_xboole_0(k3_zfmisc_1(k2_zfmisc_1(esk1_0,X1),X2,X3),k3_zfmisc_1(k2_zfmisc_1(esk5_0,X4),X5,X6)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_25])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:04:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S076A
% 0.13/0.37  # and selection function SelectCQIAr.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.026 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t64_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:(~(r1_xboole_0(k4_zfmisc_1(X1,X2,X3,X4),k4_zfmisc_1(X5,X6,X7,X8)))=>(((~(r1_xboole_0(X1,X5))&~(r1_xboole_0(X2,X6)))&~(r1_xboole_0(X3,X7)))&~(r1_xboole_0(X4,X8)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_mcart_1)).
% 0.13/0.37  fof(t54_mcart_1, axiom, ![X1, X2, X3, X4]:k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4)=k4_zfmisc_1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_mcart_1)).
% 0.13/0.37  fof(t52_mcart_1, axiom, ![X1, X2, X3, X4, X5, X6]:(~(r1_xboole_0(k3_zfmisc_1(X1,X2,X3),k3_zfmisc_1(X4,X5,X6)))=>((~(r1_xboole_0(X1,X4))&~(r1_xboole_0(X2,X5)))&~(r1_xboole_0(X3,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_mcart_1)).
% 0.13/0.37  fof(t127_zfmisc_1, axiom, ![X1, X2, X3, X4]:((r1_xboole_0(X1,X2)|r1_xboole_0(X3,X4))=>r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 0.13/0.37  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:(~(r1_xboole_0(k4_zfmisc_1(X1,X2,X3,X4),k4_zfmisc_1(X5,X6,X7,X8)))=>(((~(r1_xboole_0(X1,X5))&~(r1_xboole_0(X2,X6)))&~(r1_xboole_0(X3,X7)))&~(r1_xboole_0(X4,X8))))), inference(assume_negation,[status(cth)],[t64_mcart_1])).
% 0.13/0.37  fof(c_0_5, negated_conjecture, (~r1_xboole_0(k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))&(r1_xboole_0(esk1_0,esk5_0)|r1_xboole_0(esk2_0,esk6_0)|r1_xboole_0(esk3_0,esk7_0)|r1_xboole_0(esk4_0,esk8_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).
% 0.13/0.37  fof(c_0_6, plain, ![X19, X20, X21, X22]:k3_zfmisc_1(k2_zfmisc_1(X19,X20),X21,X22)=k4_zfmisc_1(X19,X20,X21,X22), inference(variable_rename,[status(thm)],[t54_mcart_1])).
% 0.13/0.37  fof(c_0_7, plain, ![X13, X14, X15, X16, X17, X18]:(((~r1_xboole_0(X13,X16)|r1_xboole_0(k3_zfmisc_1(X13,X14,X15),k3_zfmisc_1(X16,X17,X18)))&(~r1_xboole_0(X14,X17)|r1_xboole_0(k3_zfmisc_1(X13,X14,X15),k3_zfmisc_1(X16,X17,X18))))&(~r1_xboole_0(X15,X18)|r1_xboole_0(k3_zfmisc_1(X13,X14,X15),k3_zfmisc_1(X16,X17,X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_mcart_1])])])])).
% 0.13/0.37  cnf(c_0_8, negated_conjecture, (~r1_xboole_0(k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_9, plain, (k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4)=k4_zfmisc_1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_10, plain, (r1_xboole_0(k3_zfmisc_1(X3,X4,X1),k3_zfmisc_1(X5,X6,X2))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_11, negated_conjecture, (r1_xboole_0(esk1_0,esk5_0)|r1_xboole_0(esk2_0,esk6_0)|r1_xboole_0(esk3_0,esk7_0)|r1_xboole_0(esk4_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_12, negated_conjecture, (~r1_xboole_0(k3_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0,esk4_0),k3_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0,esk8_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_8, c_0_9]), c_0_9])).
% 0.13/0.37  cnf(c_0_13, negated_conjecture, (r1_xboole_0(k3_zfmisc_1(X1,X2,esk4_0),k3_zfmisc_1(X3,X4,esk8_0))|r1_xboole_0(esk3_0,esk7_0)|r1_xboole_0(esk2_0,esk6_0)|r1_xboole_0(esk1_0,esk5_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.13/0.37  cnf(c_0_14, plain, (r1_xboole_0(k3_zfmisc_1(X3,X1,X4),k3_zfmisc_1(X5,X2,X6))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_15, negated_conjecture, (r1_xboole_0(esk1_0,esk5_0)|r1_xboole_0(esk2_0,esk6_0)|r1_xboole_0(esk3_0,esk7_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.13/0.37  fof(c_0_16, plain, ![X9, X10, X11, X12]:((~r1_xboole_0(X9,X10)|r1_xboole_0(k2_zfmisc_1(X9,X11),k2_zfmisc_1(X10,X12)))&(~r1_xboole_0(X11,X12)|r1_xboole_0(k2_zfmisc_1(X9,X11),k2_zfmisc_1(X10,X12)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (r1_xboole_0(k3_zfmisc_1(X1,esk3_0,X2),k3_zfmisc_1(X3,esk7_0,X4))|r1_xboole_0(esk2_0,esk6_0)|r1_xboole_0(esk1_0,esk5_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.37  cnf(c_0_18, plain, (r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (r1_xboole_0(esk1_0,esk5_0)|r1_xboole_0(esk2_0,esk6_0)), inference(spm,[status(thm)],[c_0_12, c_0_17])).
% 0.13/0.37  cnf(c_0_20, plain, (r1_xboole_0(k3_zfmisc_1(X1,X3,X4),k3_zfmisc_1(X2,X5,X6))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (r1_xboole_0(k2_zfmisc_1(X1,esk2_0),k2_zfmisc_1(X2,esk6_0))|r1_xboole_0(esk1_0,esk5_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (r1_xboole_0(k3_zfmisc_1(k2_zfmisc_1(X1,esk2_0),X2,X3),k3_zfmisc_1(k2_zfmisc_1(X4,esk6_0),X5,X6))|r1_xboole_0(esk1_0,esk5_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.37  cnf(c_0_23, plain, (r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (r1_xboole_0(esk1_0,esk5_0)), inference(spm,[status(thm)],[c_0_12, c_0_22])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (r1_xboole_0(k2_zfmisc_1(esk1_0,X1),k2_zfmisc_1(esk5_0,X2))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, (r1_xboole_0(k3_zfmisc_1(k2_zfmisc_1(esk1_0,X1),X2,X3),k3_zfmisc_1(k2_zfmisc_1(esk5_0,X4),X5,X6))), inference(spm,[status(thm)],[c_0_20, c_0_25])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_26])]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 28
% 0.13/0.37  # Proof object clause steps            : 19
% 0.13/0.37  # Proof object formula steps           : 9
% 0.13/0.37  # Proof object conjectures             : 16
% 0.13/0.37  # Proof object clause conjectures      : 13
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 8
% 0.13/0.37  # Proof object initial formulas used   : 4
% 0.13/0.37  # Proof object generating inferences   : 9
% 0.13/0.37  # Proof object simplifying inferences  : 4
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 4
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 8
% 0.13/0.37  # Removed in clause preprocessing      : 1
% 0.13/0.37  # Initial clauses in saturation        : 7
% 0.13/0.37  # Processed clauses                    : 47
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 47
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 9
% 0.13/0.37  # Backward-rewritten                   : 12
% 0.13/0.37  # Generated clauses                    : 165
% 0.13/0.37  # ...of the previous two non-trivial   : 160
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 165
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 19
% 0.13/0.37  #    Positive orientable unit clauses  : 14
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 0
% 0.13/0.37  #    Non-unit-clauses                  : 5
% 0.13/0.37  # Current number of unprocessed clauses: 52
% 0.13/0.37  # ...number of literals in the above   : 52
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 29
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 162
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 129
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 9
% 0.13/0.37  # Unit Clause-clause subsumption calls : 0
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 17
% 0.13/0.37  # BW rewrite match successes           : 2
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 2884
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.031 s
% 0.13/0.37  # System time              : 0.002 s
% 0.13/0.37  # Total time               : 0.033 s
% 0.13/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
