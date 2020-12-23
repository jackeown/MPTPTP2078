%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:41:56 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 172 expanded)
%              Number of clauses        :   24 (  71 expanded)
%              Number of leaves         :    9 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   86 ( 280 expanded)
%              Number of equality atoms :   43 ( 165 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t58_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r1_xboole_0(k1_tarski(X1),X2)
      | k3_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t53_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & r2_hidden(X3,X2) )
     => k3_xboole_0(k2_tarski(X1,X3),X2) = k2_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_xboole_0(k1_tarski(X1),X2)
        | k3_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ) ),
    inference(assume_negation,[status(cth)],[t58_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X52,X53,X54,X55,X56,X57] :
      ( ( ~ r2_hidden(X54,X53)
        | X54 = X52
        | X53 != k1_tarski(X52) )
      & ( X55 != X52
        | r2_hidden(X55,X53)
        | X53 != k1_tarski(X52) )
      & ( ~ r2_hidden(esk5_2(X56,X57),X57)
        | esk5_2(X56,X57) != X56
        | X57 = k1_tarski(X56) )
      & ( r2_hidden(esk5_2(X56,X57),X57)
        | esk5_2(X56,X57) = X56
        | X57 = k1_tarski(X56) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_11,plain,(
    ! [X59] : k2_tarski(X59,X59) = k1_tarski(X59) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,plain,(
    ! [X60,X61] : k1_enumset1(X60,X60,X61) = k2_tarski(X60,X61) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X62,X63,X64] : k2_enumset1(X62,X62,X63,X64) = k1_enumset1(X62,X63,X64) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_14,negated_conjecture,
    ( ~ r1_xboole_0(k1_tarski(esk6_0),esk7_0)
    & k3_xboole_0(k1_tarski(esk6_0),esk7_0) != k1_tarski(esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_15,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( ~ r1_xboole_0(k1_tarski(esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X21,X22,X24,X25,X26] :
      ( ( r2_hidden(esk2_2(X21,X22),X21)
        | r1_xboole_0(X21,X22) )
      & ( r2_hidden(esk2_2(X21,X22),X22)
        | r1_xboole_0(X21,X22) )
      & ( ~ r2_hidden(X26,X24)
        | ~ r2_hidden(X26,X25)
        | ~ r1_xboole_0(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_21,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( ~ r1_xboole_0(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X65,X66,X67] :
      ( ~ r2_hidden(X65,X66)
      | ~ r2_hidden(X67,X66)
      | k3_xboole_0(k2_tarski(X65,X67),X66) = k2_tarski(X65,X67) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t53_zfmisc_1])])).

fof(c_0_25,plain,(
    ! [X37,X38] : k4_xboole_0(X37,k4_xboole_0(X37,X38)) = k3_xboole_0(X37,X38) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_26,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk2_2(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_29,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_30,plain,
    ( k3_xboole_0(k2_tarski(X1,X3),X2) = k2_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk2_2(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( esk2_2(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk6_0),esk7_0) != k1_tarski(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_36,plain,
    ( k4_xboole_0(k2_enumset1(X1,X1,X1,X3),k4_xboole_0(k2_enumset1(X1,X1,X1,X3),X2)) = k2_enumset1(X1,X1,X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_17]),c_0_17]),c_0_18]),c_0_18]),c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_31]),c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),k4_xboole_0(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)) != k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_16]),c_0_16]),c_0_17]),c_0_17]),c_0_18]),c_0_18]),c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( k4_xboole_0(esk7_0,k4_xboole_0(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,X1))) = k2_enumset1(esk6_0,esk6_0,esk6_0,X1)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( k4_xboole_0(esk7_0,k4_xboole_0(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))) != k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_39,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_37]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:17:24 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.13/0.38  # and selection function SelectNegativeLiterals.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.029 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t58_zfmisc_1, conjecture, ![X1, X2]:(r1_xboole_0(k1_tarski(X1),X2)|k3_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 0.13/0.38  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.13/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.38  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.13/0.38  fof(t53_zfmisc_1, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&r2_hidden(X3,X2))=>k3_xboole_0(k2_tarski(X1,X3),X2)=k2_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_zfmisc_1)).
% 0.13/0.38  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.13/0.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.13/0.38  fof(c_0_9, negated_conjecture, ~(![X1, X2]:(r1_xboole_0(k1_tarski(X1),X2)|k3_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1))), inference(assume_negation,[status(cth)],[t58_zfmisc_1])).
% 0.13/0.38  fof(c_0_10, plain, ![X52, X53, X54, X55, X56, X57]:(((~r2_hidden(X54,X53)|X54=X52|X53!=k1_tarski(X52))&(X55!=X52|r2_hidden(X55,X53)|X53!=k1_tarski(X52)))&((~r2_hidden(esk5_2(X56,X57),X57)|esk5_2(X56,X57)!=X56|X57=k1_tarski(X56))&(r2_hidden(esk5_2(X56,X57),X57)|esk5_2(X56,X57)=X56|X57=k1_tarski(X56)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.13/0.38  fof(c_0_11, plain, ![X59]:k2_tarski(X59,X59)=k1_tarski(X59), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.38  fof(c_0_12, plain, ![X60, X61]:k1_enumset1(X60,X60,X61)=k2_tarski(X60,X61), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  fof(c_0_13, plain, ![X62, X63, X64]:k2_enumset1(X62,X62,X63,X64)=k1_enumset1(X62,X63,X64), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.38  fof(c_0_14, negated_conjecture, (~r1_xboole_0(k1_tarski(esk6_0),esk7_0)&k3_xboole_0(k1_tarski(esk6_0),esk7_0)!=k1_tarski(esk6_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.13/0.38  cnf(c_0_15, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_16, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_18, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (~r1_xboole_0(k1_tarski(esk6_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  fof(c_0_20, plain, ![X21, X22, X24, X25, X26]:(((r2_hidden(esk2_2(X21,X22),X21)|r1_xboole_0(X21,X22))&(r2_hidden(esk2_2(X21,X22),X22)|r1_xboole_0(X21,X22)))&(~r2_hidden(X26,X24)|~r2_hidden(X26,X25)|~r1_xboole_0(X24,X25))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.13/0.38  cnf(c_0_21, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (~r1_xboole_0(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_16]), c_0_17]), c_0_18])).
% 0.13/0.38  cnf(c_0_23, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  fof(c_0_24, plain, ![X65, X66, X67]:(~r2_hidden(X65,X66)|~r2_hidden(X67,X66)|k3_xboole_0(k2_tarski(X65,X67),X66)=k2_tarski(X65,X67)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t53_zfmisc_1])])).
% 0.13/0.38  fof(c_0_25, plain, ![X37, X38]:k4_xboole_0(X37,k4_xboole_0(X37,X38))=k3_xboole_0(X37,X38), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.13/0.38  cnf(c_0_26, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_27, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (r2_hidden(esk2_2(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.38  fof(c_0_29, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.13/0.38  cnf(c_0_30, plain, (k3_xboole_0(k2_tarski(X1,X3),X2)=k2_tarski(X1,X3)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_31, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (r2_hidden(esk2_2(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_22, c_0_26])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (esk2_2(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)=esk6_0), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.38  cnf(c_0_34, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (k3_xboole_0(k1_tarski(esk6_0),esk7_0)!=k1_tarski(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_36, plain, (k4_xboole_0(k2_enumset1(X1,X1,X1,X3),k4_xboole_0(k2_enumset1(X1,X1,X1,X3),X2))=k2_enumset1(X1,X1,X1,X3)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_17]), c_0_17]), c_0_18]), c_0_18]), c_0_31])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (r2_hidden(esk6_0,esk7_0)), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.38  cnf(c_0_38, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_31]), c_0_31])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (k4_xboole_0(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),k4_xboole_0(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0))!=k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_16]), c_0_16]), c_0_17]), c_0_17]), c_0_18]), c_0_18]), c_0_31])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (k4_xboole_0(esk7_0,k4_xboole_0(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,X1)))=k2_enumset1(esk6_0,esk6_0,esk6_0,X1)|~r2_hidden(X1,esk7_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (k4_xboole_0(esk7_0,k4_xboole_0(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)))!=k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[c_0_39, c_0_38])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_37]), c_0_41]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 43
% 0.13/0.38  # Proof object clause steps            : 24
% 0.13/0.38  # Proof object formula steps           : 19
% 0.13/0.38  # Proof object conjectures             : 14
% 0.13/0.38  # Proof object clause conjectures      : 11
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 11
% 0.13/0.38  # Proof object initial formulas used   : 9
% 0.13/0.38  # Proof object generating inferences   : 5
% 0.13/0.38  # Proof object simplifying inferences  : 25
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 18
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 39
% 0.13/0.38  # Removed in clause preprocessing      : 4
% 0.13/0.38  # Initial clauses in saturation        : 35
% 0.13/0.38  # Processed clauses                    : 255
% 0.13/0.38  # ...of these trivial                  : 7
% 0.13/0.38  # ...subsumed                          : 111
% 0.13/0.38  # ...remaining for further processing  : 137
% 0.13/0.38  # Other redundant clauses eliminated   : 66
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 10
% 0.13/0.38  # Generated clauses                    : 1086
% 0.13/0.38  # ...of the previous two non-trivial   : 902
% 0.13/0.38  # Contextual simplify-reflections      : 1
% 0.13/0.38  # Paramodulations                      : 1018
% 0.13/0.38  # Factorizations                       : 6
% 0.13/0.38  # Equation resolutions                 : 66
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 84
% 0.13/0.38  #    Positive orientable unit clauses  : 20
% 0.13/0.38  #    Positive unorientable unit clauses: 1
% 0.13/0.38  #    Negative unit clauses             : 10
% 0.13/0.38  #    Non-unit-clauses                  : 53
% 0.13/0.38  # Current number of unprocessed clauses: 698
% 0.13/0.38  # ...number of literals in the above   : 2101
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 48
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 536
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 395
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 20
% 0.13/0.38  # Unit Clause-clause subsumption calls : 31
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 31
% 0.13/0.38  # BW rewrite match successes           : 17
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 15066
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.048 s
% 0.13/0.38  # System time              : 0.002 s
% 0.13/0.38  # Total time               : 0.050 s
% 0.13/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
