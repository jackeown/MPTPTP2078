%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:37 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 (  72 expanded)
%              Number of clauses        :   23 (  32 expanded)
%              Number of leaves         :   10 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :   59 (  90 expanded)
%              Number of equality atoms :   30 (  55 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t80_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(c_0_10,plain,(
    ! [X4,X5,X7,X8,X9] :
      ( ( r1_xboole_0(X4,X5)
        | r2_hidden(esk1_2(X4,X5),k3_xboole_0(X4,X5)) )
      & ( ~ r2_hidden(X9,k3_xboole_0(X7,X8))
        | ~ r1_xboole_0(X7,X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_11,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X10] :
      ( X10 = k1_xboole_0
      | r2_hidden(esk2_1(X10),X10) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_xboole_0(X1,X2)
       => r1_xboole_0(X1,k4_xboole_0(X2,X3)) ) ),
    inference(assume_negation,[status(cth)],[t80_xboole_1])).

fof(c_0_16,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k3_xboole_0(X14,X15)) = k4_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_17,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0)
    & ~ r1_xboole_0(esk3_0,k4_xboole_0(esk4_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_20,plain,(
    ! [X12] : k3_xboole_0(X12,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_21,plain,(
    ! [X18,X19,X20] : k3_xboole_0(X18,k4_xboole_0(X19,X20)) = k4_xboole_0(k3_xboole_0(X18,X19),X20) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X13] : k4_xboole_0(X13,k1_xboole_0) = X13 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_26,c_0_13])).

fof(c_0_32,plain,(
    ! [X21] : k4_xboole_0(k1_xboole_0,X21) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_13]),c_0_13])).

cnf(c_0_34,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_36,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_37,plain,(
    ! [X22,X23] : r1_xboole_0(k4_xboole_0(X22,X23),X23) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_38,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_39,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,X1)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_38]),c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( ~ r1_xboole_0(esk3_0,k4_xboole_0(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_42,negated_conjecture,
    ( r1_xboole_0(esk3_0,k4_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:30:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___103_C18_F1_PI_AE_Q4_CS_SP_S0Y
% 0.20/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.027 s
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.20/0.37  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.37  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.20/0.37  fof(t80_xboole_1, conjecture, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_xboole_1)).
% 0.20/0.37  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.20/0.37  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.20/0.37  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.20/0.37  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.20/0.37  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.20/0.37  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.20/0.37  fof(c_0_10, plain, ![X4, X5, X7, X8, X9]:((r1_xboole_0(X4,X5)|r2_hidden(esk1_2(X4,X5),k3_xboole_0(X4,X5)))&(~r2_hidden(X9,k3_xboole_0(X7,X8))|~r1_xboole_0(X7,X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.20/0.37  fof(c_0_11, plain, ![X16, X17]:k4_xboole_0(X16,k4_xboole_0(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.37  cnf(c_0_12, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.37  cnf(c_0_13, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.37  fof(c_0_14, plain, ![X10]:(X10=k1_xboole_0|r2_hidden(esk2_1(X10),X10)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.20/0.37  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X2,X3)))), inference(assume_negation,[status(cth)],[t80_xboole_1])).
% 0.20/0.37  fof(c_0_16, plain, ![X14, X15]:k4_xboole_0(X14,k3_xboole_0(X14,X15))=k4_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.20/0.37  cnf(c_0_17, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.37  cnf(c_0_18, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.37  fof(c_0_19, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)&~r1_xboole_0(esk3_0,k4_xboole_0(esk4_0,esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.20/0.37  fof(c_0_20, plain, ![X12]:k3_xboole_0(X12,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.20/0.37  fof(c_0_21, plain, ![X18, X19, X20]:k3_xboole_0(X18,k4_xboole_0(X19,X20))=k4_xboole_0(k3_xboole_0(X18,X19),X20), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.20/0.37  cnf(c_0_22, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.37  cnf(c_0_23, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.37  cnf(c_0_24, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.37  fof(c_0_25, plain, ![X13]:k4_xboole_0(X13,k1_xboole_0)=X13, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.20/0.37  cnf(c_0_26, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.37  cnf(c_0_27, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.37  cnf(c_0_28, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_13])).
% 0.20/0.37  cnf(c_0_29, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.37  cnf(c_0_30, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.37  cnf(c_0_31, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_26, c_0_13])).
% 0.20/0.37  fof(c_0_32, plain, ![X21]:k4_xboole_0(k1_xboole_0,X21)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.20/0.37  cnf(c_0_33, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_13]), c_0_13])).
% 0.20/0.37  cnf(c_0_34, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.20/0.37  cnf(c_0_35, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_31, c_0_30])).
% 0.20/0.37  cnf(c_0_36, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.37  fof(c_0_37, plain, ![X22, X23]:r1_xboole_0(k4_xboole_0(X22,X23),X23), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.20/0.37  cnf(c_0_38, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36])).
% 0.20/0.37  cnf(c_0_39, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.37  cnf(c_0_40, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,X1))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_38]), c_0_30])).
% 0.20/0.37  cnf(c_0_41, negated_conjecture, (~r1_xboole_0(esk3_0,k4_xboole_0(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.37  cnf(c_0_42, negated_conjecture, (r1_xboole_0(esk3_0,k4_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.37  cnf(c_0_43, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42])]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 44
% 0.20/0.37  # Proof object clause steps            : 23
% 0.20/0.37  # Proof object formula steps           : 21
% 0.20/0.37  # Proof object conjectures             : 11
% 0.20/0.37  # Proof object clause conjectures      : 8
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 11
% 0.20/0.37  # Proof object initial formulas used   : 10
% 0.20/0.37  # Proof object generating inferences   : 6
% 0.20/0.37  # Proof object simplifying inferences  : 12
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 10
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 12
% 0.20/0.37  # Removed in clause preprocessing      : 1
% 0.20/0.37  # Initial clauses in saturation        : 11
% 0.20/0.37  # Processed clauses                    : 52
% 0.20/0.37  # ...of these trivial                  : 3
% 0.20/0.37  # ...subsumed                          : 18
% 0.20/0.37  # ...remaining for further processing  : 31
% 0.20/0.37  # Other redundant clauses eliminated   : 0
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 3
% 0.20/0.37  # Generated clauses                    : 266
% 0.20/0.37  # ...of the previous two non-trivial   : 141
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 266
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
% 0.20/0.37  # Current number of processed clauses  : 28
% 0.20/0.37  #    Positive orientable unit clauses  : 16
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 1
% 0.20/0.37  #    Non-unit-clauses                  : 11
% 0.20/0.37  # Current number of unprocessed clauses: 91
% 0.20/0.37  # ...number of literals in the above   : 131
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 4
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 26
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 26
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 12
% 0.20/0.38  # Unit Clause-clause subsumption calls : 2
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 13
% 0.20/0.38  # BW rewrite match successes           : 3
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 3735
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.030 s
% 0.20/0.38  # System time              : 0.003 s
% 0.20/0.38  # Total time               : 0.033 s
% 0.20/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
