%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:41:56 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
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
    ! [X51,X52,X53,X54,X55,X56] :
      ( ( ~ r2_hidden(X53,X52)
        | X53 = X51
        | X52 != k1_tarski(X51) )
      & ( X54 != X51
        | r2_hidden(X54,X52)
        | X52 != k1_tarski(X51) )
      & ( ~ r2_hidden(esk5_2(X55,X56),X56)
        | esk5_2(X55,X56) != X55
        | X56 = k1_tarski(X55) )
      & ( r2_hidden(esk5_2(X55,X56),X56)
        | esk5_2(X55,X56) = X55
        | X56 = k1_tarski(X55) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_11,plain,(
    ! [X58] : k2_tarski(X58,X58) = k1_tarski(X58) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,plain,(
    ! [X59,X60] : k1_enumset1(X59,X59,X60) = k2_tarski(X59,X60) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X61,X62,X63] : k2_enumset1(X61,X61,X62,X63) = k1_enumset1(X61,X62,X63) ),
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
    ! [X19,X20,X22,X23,X24] :
      ( ( r2_hidden(esk2_2(X19,X20),X19)
        | r1_xboole_0(X19,X20) )
      & ( r2_hidden(esk2_2(X19,X20),X20)
        | r1_xboole_0(X19,X20) )
      & ( ~ r2_hidden(X24,X22)
        | ~ r2_hidden(X24,X23)
        | ~ r1_xboole_0(X22,X23) ) ) ),
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
    ! [X64,X65,X66] :
      ( ~ r2_hidden(X64,X65)
      | ~ r2_hidden(X66,X65)
      | k3_xboole_0(k2_tarski(X64,X66),X65) = k2_tarski(X64,X66) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t53_zfmisc_1])])).

fof(c_0_25,plain,(
    ! [X35,X36] : k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k3_xboole_0(X35,X36) ),
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:36:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.20/0.43  # and selection function SelectNegativeLiterals.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.041 s
% 0.20/0.43  # Presaturation interreduction done
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(t58_zfmisc_1, conjecture, ![X1, X2]:(r1_xboole_0(k1_tarski(X1),X2)|k3_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 0.20/0.43  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.20/0.43  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.43  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.43  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.43  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.43  fof(t53_zfmisc_1, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&r2_hidden(X3,X2))=>k3_xboole_0(k2_tarski(X1,X3),X2)=k2_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_zfmisc_1)).
% 0.20/0.43  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.43  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.43  fof(c_0_9, negated_conjecture, ~(![X1, X2]:(r1_xboole_0(k1_tarski(X1),X2)|k3_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1))), inference(assume_negation,[status(cth)],[t58_zfmisc_1])).
% 0.20/0.43  fof(c_0_10, plain, ![X51, X52, X53, X54, X55, X56]:(((~r2_hidden(X53,X52)|X53=X51|X52!=k1_tarski(X51))&(X54!=X51|r2_hidden(X54,X52)|X52!=k1_tarski(X51)))&((~r2_hidden(esk5_2(X55,X56),X56)|esk5_2(X55,X56)!=X55|X56=k1_tarski(X55))&(r2_hidden(esk5_2(X55,X56),X56)|esk5_2(X55,X56)=X55|X56=k1_tarski(X55)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.20/0.43  fof(c_0_11, plain, ![X58]:k2_tarski(X58,X58)=k1_tarski(X58), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.43  fof(c_0_12, plain, ![X59, X60]:k1_enumset1(X59,X59,X60)=k2_tarski(X59,X60), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.43  fof(c_0_13, plain, ![X61, X62, X63]:k2_enumset1(X61,X61,X62,X63)=k1_enumset1(X61,X62,X63), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.43  fof(c_0_14, negated_conjecture, (~r1_xboole_0(k1_tarski(esk6_0),esk7_0)&k3_xboole_0(k1_tarski(esk6_0),esk7_0)!=k1_tarski(esk6_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.20/0.43  cnf(c_0_15, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.43  cnf(c_0_16, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.43  cnf(c_0_18, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.43  cnf(c_0_19, negated_conjecture, (~r1_xboole_0(k1_tarski(esk6_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.43  fof(c_0_20, plain, ![X19, X20, X22, X23, X24]:(((r2_hidden(esk2_2(X19,X20),X19)|r1_xboole_0(X19,X20))&(r2_hidden(esk2_2(X19,X20),X20)|r1_xboole_0(X19,X20)))&(~r2_hidden(X24,X22)|~r2_hidden(X24,X23)|~r1_xboole_0(X22,X23))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.43  cnf(c_0_21, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])).
% 0.20/0.43  cnf(c_0_22, negated_conjecture, (~r1_xboole_0(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_16]), c_0_17]), c_0_18])).
% 0.20/0.43  cnf(c_0_23, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.43  fof(c_0_24, plain, ![X64, X65, X66]:(~r2_hidden(X64,X65)|~r2_hidden(X66,X65)|k3_xboole_0(k2_tarski(X64,X66),X65)=k2_tarski(X64,X66)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t53_zfmisc_1])])).
% 0.20/0.43  fof(c_0_25, plain, ![X35, X36]:k4_xboole_0(X35,k4_xboole_0(X35,X36))=k3_xboole_0(X35,X36), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.43  cnf(c_0_26, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.43  cnf(c_0_27, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_21])).
% 0.20/0.43  cnf(c_0_28, negated_conjecture, (r2_hidden(esk2_2(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.43  fof(c_0_29, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.43  cnf(c_0_30, plain, (k3_xboole_0(k2_tarski(X1,X3),X2)=k2_tarski(X1,X3)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.43  cnf(c_0_31, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.43  cnf(c_0_32, negated_conjecture, (r2_hidden(esk2_2(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_22, c_0_26])).
% 0.20/0.43  cnf(c_0_33, negated_conjecture, (esk2_2(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)=esk6_0), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.43  cnf(c_0_34, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.43  cnf(c_0_35, negated_conjecture, (k3_xboole_0(k1_tarski(esk6_0),esk7_0)!=k1_tarski(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.43  cnf(c_0_36, plain, (k4_xboole_0(k2_enumset1(X1,X1,X1,X3),k4_xboole_0(k2_enumset1(X1,X1,X1,X3),X2))=k2_enumset1(X1,X1,X1,X3)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_17]), c_0_17]), c_0_18]), c_0_18]), c_0_31])).
% 0.20/0.43  cnf(c_0_37, negated_conjecture, (r2_hidden(esk6_0,esk7_0)), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.43  cnf(c_0_38, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_31]), c_0_31])).
% 0.20/0.43  cnf(c_0_39, negated_conjecture, (k4_xboole_0(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),k4_xboole_0(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0))!=k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_16]), c_0_16]), c_0_17]), c_0_17]), c_0_18]), c_0_18]), c_0_31])).
% 0.20/0.43  cnf(c_0_40, negated_conjecture, (k4_xboole_0(esk7_0,k4_xboole_0(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,X1)))=k2_enumset1(esk6_0,esk6_0,esk6_0,X1)|~r2_hidden(X1,esk7_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 0.20/0.43  cnf(c_0_41, negated_conjecture, (k4_xboole_0(esk7_0,k4_xboole_0(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)))!=k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[c_0_39, c_0_38])).
% 0.20/0.43  cnf(c_0_42, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_37]), c_0_41]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 43
% 0.20/0.43  # Proof object clause steps            : 24
% 0.20/0.43  # Proof object formula steps           : 19
% 0.20/0.43  # Proof object conjectures             : 14
% 0.20/0.43  # Proof object clause conjectures      : 11
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 11
% 0.20/0.43  # Proof object initial formulas used   : 9
% 0.20/0.43  # Proof object generating inferences   : 5
% 0.20/0.43  # Proof object simplifying inferences  : 25
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 18
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 39
% 0.20/0.43  # Removed in clause preprocessing      : 4
% 0.20/0.43  # Initial clauses in saturation        : 35
% 0.20/0.43  # Processed clauses                    : 268
% 0.20/0.43  # ...of these trivial                  : 13
% 0.20/0.43  # ...subsumed                          : 111
% 0.20/0.43  # ...remaining for further processing  : 144
% 0.20/0.43  # Other redundant clauses eliminated   : 85
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 0
% 0.20/0.43  # Backward-rewritten                   : 13
% 0.20/0.43  # Generated clauses                    : 1428
% 0.20/0.43  # ...of the previous two non-trivial   : 1157
% 0.20/0.43  # Contextual simplify-reflections      : 1
% 0.20/0.43  # Paramodulations                      : 1341
% 0.20/0.43  # Factorizations                       : 6
% 0.20/0.43  # Equation resolutions                 : 85
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 88
% 0.20/0.43  #    Positive orientable unit clauses  : 22
% 0.20/0.43  #    Positive unorientable unit clauses: 1
% 0.20/0.43  #    Negative unit clauses             : 9
% 0.20/0.43  #    Non-unit-clauses                  : 56
% 0.20/0.43  # Current number of unprocessed clauses: 934
% 0.20/0.43  # ...number of literals in the above   : 2677
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 51
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 619
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 442
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 22
% 0.20/0.43  # Unit Clause-clause subsumption calls : 40
% 0.20/0.43  # Rewrite failures with RHS unbound    : 0
% 0.20/0.43  # BW rewrite match attempts            : 36
% 0.20/0.43  # BW rewrite match successes           : 19
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 18470
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.076 s
% 0.20/0.43  # System time              : 0.005 s
% 0.20/0.43  # Total time               : 0.081 s
% 0.20/0.43  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
