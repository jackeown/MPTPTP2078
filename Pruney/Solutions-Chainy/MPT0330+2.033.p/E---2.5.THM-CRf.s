%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:30 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   31 (  54 expanded)
%              Number of clauses        :   16 (  23 expanded)
%              Number of leaves         :    7 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :   66 ( 119 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t143_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
        & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
     => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t119_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
          & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
       => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    inference(assume_negation,[status(cth)],[t143_zfmisc_1])).

fof(c_0_8,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | ~ r1_tarski(X10,X11)
      | r1_tarski(X9,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_9,plain,(
    ! [X22,X23,X24,X25] :
      ( ~ r1_tarski(X22,X23)
      | ~ r1_tarski(X24,X25)
      | r1_tarski(k2_zfmisc_1(X22,X24),k2_zfmisc_1(X23,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t119_zfmisc_1])])).

fof(c_0_10,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))
    & r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))
    & ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_11,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_tarski(X19,X20)
      | ~ r1_tarski(X21,X20)
      | r1_tarski(k2_xboole_0(X19,X21),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(k4_xboole_0(X14,X15),X16)
      | r1_tarski(X14,k2_xboole_0(X15,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

fof(c_0_15,plain,(
    ! [X12,X13] : r1_tarski(k4_xboole_0(X12,X13),X12) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_16,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r1_tarski(X1,k2_zfmisc_1(X4,X5))
    | ~ r1_tarski(X5,X3)
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))
    | ~ r1_tarski(esk1_0,k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(X1,X2))
    | ~ r1_tarski(esk6_0,X2)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_26,plain,(
    ! [X17,X18] : r1_tarski(X17,k2_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_27,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_24])])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(X1,X2))
    | ~ r1_tarski(esk4_0,X2)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_25])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:38:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.57  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S061I
% 0.20/0.57  # and selection function SelectMaxLComplexAPPNTNp.
% 0.20/0.57  #
% 0.20/0.57  # Preprocessing time       : 0.027 s
% 0.20/0.57  # Presaturation interreduction done
% 0.20/0.57  
% 0.20/0.57  # Proof found!
% 0.20/0.57  # SZS status Theorem
% 0.20/0.57  # SZS output start CNFRefutation
% 0.20/0.57  fof(t143_zfmisc_1, conjecture, ![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 0.20/0.57  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.20/0.57  fof(t119_zfmisc_1, axiom, ![X1, X2, X3, X4]:((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 0.20/0.57  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.20/0.57  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.20/0.57  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.20/0.57  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.20/0.57  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))))), inference(assume_negation,[status(cth)],[t143_zfmisc_1])).
% 0.20/0.57  fof(c_0_8, plain, ![X9, X10, X11]:(~r1_tarski(X9,X10)|~r1_tarski(X10,X11)|r1_tarski(X9,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.20/0.57  fof(c_0_9, plain, ![X22, X23, X24, X25]:(~r1_tarski(X22,X23)|~r1_tarski(X24,X25)|r1_tarski(k2_zfmisc_1(X22,X24),k2_zfmisc_1(X23,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t119_zfmisc_1])])).
% 0.20/0.57  fof(c_0_10, negated_conjecture, ((r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))&r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)))&~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.20/0.57  fof(c_0_11, plain, ![X19, X20, X21]:(~r1_tarski(X19,X20)|~r1_tarski(X21,X20)|r1_tarski(k2_xboole_0(X19,X21),X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.20/0.57  cnf(c_0_12, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.57  cnf(c_0_13, plain, (r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.57  fof(c_0_14, plain, ![X14, X15, X16]:(~r1_tarski(k4_xboole_0(X14,X15),X16)|r1_tarski(X14,k2_xboole_0(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.20/0.57  fof(c_0_15, plain, ![X12, X13]:r1_tarski(k4_xboole_0(X12,X13),X12), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.20/0.57  cnf(c_0_16, negated_conjecture, (~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.57  cnf(c_0_17, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.57  cnf(c_0_18, plain, (r1_tarski(X1,k2_zfmisc_1(X2,X3))|~r1_tarski(X1,k2_zfmisc_1(X4,X5))|~r1_tarski(X5,X3)|~r1_tarski(X4,X2)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.57  cnf(c_0_19, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.57  cnf(c_0_20, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.57  cnf(c_0_21, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.57  cnf(c_0_22, negated_conjecture, (~r1_tarski(esk2_0,k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))|~r1_tarski(esk1_0,k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.57  cnf(c_0_23, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(X1,X2))|~r1_tarski(esk6_0,X2)|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.57  cnf(c_0_24, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.57  cnf(c_0_25, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.57  fof(c_0_26, plain, ![X17, X18]:r1_tarski(X17,k2_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.20/0.57  cnf(c_0_27, negated_conjecture, (~r1_tarski(esk1_0,k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_24])])).
% 0.20/0.57  cnf(c_0_28, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(X1,X2))|~r1_tarski(esk4_0,X2)|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_18, c_0_25])).
% 0.20/0.57  cnf(c_0_29, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.57  cnf(c_0_30, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_29])]), ['proof']).
% 0.20/0.57  # SZS output end CNFRefutation
% 0.20/0.57  # Proof object total steps             : 31
% 0.20/0.57  # Proof object clause steps            : 16
% 0.20/0.57  # Proof object formula steps           : 15
% 0.20/0.57  # Proof object conjectures             : 11
% 0.20/0.57  # Proof object clause conjectures      : 8
% 0.20/0.57  # Proof object formula conjectures     : 3
% 0.20/0.57  # Proof object initial clauses used    : 9
% 0.20/0.57  # Proof object initial formulas used   : 7
% 0.20/0.57  # Proof object generating inferences   : 7
% 0.20/0.57  # Proof object simplifying inferences  : 6
% 0.20/0.57  # Training examples: 0 positive, 0 negative
% 0.20/0.57  # Parsed axioms                        : 8
% 0.20/0.57  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.57  # Initial clauses                      : 12
% 0.20/0.57  # Removed in clause preprocessing      : 0
% 0.20/0.57  # Initial clauses in saturation        : 12
% 0.20/0.57  # Processed clauses                    : 2327
% 0.20/0.57  # ...of these trivial                  : 58
% 0.20/0.57  # ...subsumed                          : 1630
% 0.20/0.57  # ...remaining for further processing  : 639
% 0.20/0.57  # Other redundant clauses eliminated   : 2
% 0.20/0.57  # Clauses deleted for lack of memory   : 0
% 0.20/0.57  # Backward-subsumed                    : 35
% 0.20/0.57  # Backward-rewritten                   : 2
% 0.20/0.57  # Generated clauses                    : 19536
% 0.20/0.57  # ...of the previous two non-trivial   : 17204
% 0.20/0.57  # Contextual simplify-reflections      : 0
% 0.20/0.57  # Paramodulations                      : 19534
% 0.20/0.57  # Factorizations                       : 0
% 0.20/0.57  # Equation resolutions                 : 2
% 0.20/0.57  # Propositional unsat checks           : 0
% 0.20/0.57  #    Propositional check models        : 0
% 0.20/0.57  #    Propositional check unsatisfiable : 0
% 0.20/0.57  #    Propositional clauses             : 0
% 0.20/0.57  #    Propositional clauses after purity: 0
% 0.20/0.57  #    Propositional unsat core size     : 0
% 0.20/0.57  #    Propositional preprocessing time  : 0.000
% 0.20/0.57  #    Propositional encoding time       : 0.000
% 0.20/0.57  #    Propositional solver time         : 0.000
% 0.20/0.57  #    Success case prop preproc time    : 0.000
% 0.20/0.57  #    Success case prop encoding time   : 0.000
% 0.20/0.57  #    Success case prop solver time     : 0.000
% 0.20/0.57  # Current number of processed clauses  : 589
% 0.20/0.57  #    Positive orientable unit clauses  : 105
% 0.20/0.57  #    Positive unorientable unit clauses: 0
% 0.20/0.57  #    Negative unit clauses             : 3
% 0.20/0.57  #    Non-unit-clauses                  : 481
% 0.20/0.57  # Current number of unprocessed clauses: 14846
% 0.20/0.57  # ...number of literals in the above   : 32110
% 0.20/0.57  # Current number of archived formulas  : 0
% 0.20/0.57  # Current number of archived clauses   : 48
% 0.20/0.57  # Clause-clause subsumption calls (NU) : 38357
% 0.20/0.57  # Rec. Clause-clause subsumption calls : 35327
% 0.20/0.57  # Non-unit clause-clause subsumptions  : 1665
% 0.20/0.57  # Unit Clause-clause subsumption calls : 205
% 0.20/0.57  # Rewrite failures with RHS unbound    : 0
% 0.20/0.57  # BW rewrite match attempts            : 334
% 0.20/0.57  # BW rewrite match successes           : 2
% 0.20/0.57  # Condensation attempts                : 0
% 0.20/0.57  # Condensation successes               : 0
% 0.20/0.57  # Termbank termtop insertions          : 253927
% 0.20/0.57  
% 0.20/0.57  # -------------------------------------------------
% 0.20/0.57  # User time                : 0.228 s
% 0.20/0.57  # System time              : 0.010 s
% 0.20/0.57  # Total time               : 0.238 s
% 0.20/0.57  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
