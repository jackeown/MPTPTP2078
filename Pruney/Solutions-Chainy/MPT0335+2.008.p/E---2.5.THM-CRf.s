%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:41 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 180 expanded)
%              Number of clauses        :   29 (  73 expanded)
%              Number of leaves         :   10 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :   68 ( 237 expanded)
%              Number of equality atoms :   45 ( 187 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t148_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & k3_xboole_0(X2,X3) = k1_tarski(X4)
        & r2_hidden(X4,X1) )
     => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(X1,X2)
          & k3_xboole_0(X2,X3) = k1_tarski(X4)
          & r2_hidden(X4,X1) )
       => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    inference(assume_negation,[status(cth)],[t148_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X40,X41] :
      ( ( ~ r1_tarski(k1_tarski(X40),X41)
        | r2_hidden(X40,X41) )
      & ( ~ r2_hidden(X40,X41)
        | r1_tarski(k1_tarski(X40),X41) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_12,plain,(
    ! [X34] : k2_tarski(X34,X34) = k1_tarski(X34) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_13,plain,(
    ! [X35,X36] : k1_enumset1(X35,X35,X36) = k2_tarski(X35,X36) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X37,X38,X39] : k2_enumset1(X37,X37,X38,X39) = k1_enumset1(X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_15,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    & k3_xboole_0(esk4_0,esk5_0) = k1_tarski(esk6_0)
    & r2_hidden(esk6_0,esk3_0)
    & k3_xboole_0(esk3_0,esk5_0) != k1_tarski(esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_16,plain,(
    ! [X32,X33] : k4_xboole_0(X32,k4_xboole_0(X32,X33)) = k3_xboole_0(X32,X33) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_17,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk5_0) = k1_tarski(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X30,X31] : k3_xboole_0(X30,k2_xboole_0(X30,X31)) = X30 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

fof(c_0_24,plain,(
    ! [X25,X26] :
      ( ~ r1_tarski(X25,X26)
      | k2_xboole_0(X25,X26) = X26 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_25,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk6_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)) = k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_18]),c_0_19]),c_0_20]),c_0_22])).

fof(c_0_28,plain,(
    ! [X27,X28,X29] : k3_xboole_0(k3_xboole_0(X27,X28),X29) = k3_xboole_0(X27,k3_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

fof(c_0_29,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)),esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_33,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_30,c_0_22])).

cnf(c_0_37,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)),esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_22]),c_0_22]),c_0_22]),c_0_22])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_22]),c_0_22])).

cnf(c_0_40,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) != k1_tarski(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_42,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0)))) = k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0)) != k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_18]),c_0_19]),c_0_20]),c_0_22])).

cnf(c_0_46,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)))) = k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1)))) = k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)) != k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_45,c_0_27])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_48]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:01:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.12/0.40  # and selection function SelectCQArNTNpEqFirst.
% 0.12/0.40  #
% 0.12/0.40  # Preprocessing time       : 0.022 s
% 0.12/0.40  # Presaturation interreduction done
% 0.12/0.40  
% 0.12/0.40  # Proof found!
% 0.12/0.40  # SZS status Theorem
% 0.12/0.40  # SZS output start CNFRefutation
% 0.12/0.40  fof(t148_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 0.12/0.40  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.12/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.40  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.12/0.40  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.12/0.40  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.12/0.40  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.12/0.40  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.12/0.40  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4))), inference(assume_negation,[status(cth)],[t148_zfmisc_1])).
% 0.12/0.40  fof(c_0_11, plain, ![X40, X41]:((~r1_tarski(k1_tarski(X40),X41)|r2_hidden(X40,X41))&(~r2_hidden(X40,X41)|r1_tarski(k1_tarski(X40),X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.12/0.40  fof(c_0_12, plain, ![X34]:k2_tarski(X34,X34)=k1_tarski(X34), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.40  fof(c_0_13, plain, ![X35, X36]:k1_enumset1(X35,X35,X36)=k2_tarski(X35,X36), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.40  fof(c_0_14, plain, ![X37, X38, X39]:k2_enumset1(X37,X37,X38,X39)=k1_enumset1(X37,X38,X39), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.40  fof(c_0_15, negated_conjecture, (((r1_tarski(esk3_0,esk4_0)&k3_xboole_0(esk4_0,esk5_0)=k1_tarski(esk6_0))&r2_hidden(esk6_0,esk3_0))&k3_xboole_0(esk3_0,esk5_0)!=k1_tarski(esk6_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.12/0.40  fof(c_0_16, plain, ![X32, X33]:k4_xboole_0(X32,k4_xboole_0(X32,X33))=k3_xboole_0(X32,X33), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.12/0.40  cnf(c_0_17, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.40  cnf(c_0_18, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.40  cnf(c_0_19, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.40  cnf(c_0_20, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.40  cnf(c_0_21, negated_conjecture, (k3_xboole_0(esk4_0,esk5_0)=k1_tarski(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.40  cnf(c_0_22, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.40  fof(c_0_23, plain, ![X30, X31]:k3_xboole_0(X30,k2_xboole_0(X30,X31))=X30, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.12/0.40  fof(c_0_24, plain, ![X25, X26]:(~r1_tarski(X25,X26)|k2_xboole_0(X25,X26)=X26), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.12/0.40  cnf(c_0_25, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20])).
% 0.12/0.40  cnf(c_0_26, negated_conjecture, (r2_hidden(esk6_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.40  cnf(c_0_27, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))=k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_18]), c_0_19]), c_0_20]), c_0_22])).
% 0.12/0.40  fof(c_0_28, plain, ![X27, X28, X29]:k3_xboole_0(k3_xboole_0(X27,X28),X29)=k3_xboole_0(X27,k3_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.12/0.40  fof(c_0_29, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.12/0.40  cnf(c_0_30, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.40  cnf(c_0_31, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.40  cnf(c_0_32, negated_conjecture, (r1_tarski(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)),esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.12/0.40  cnf(c_0_33, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.40  cnf(c_0_34, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.40  cnf(c_0_35, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.40  cnf(c_0_36, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_30, c_0_22])).
% 0.12/0.40  cnf(c_0_37, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)),esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.12/0.40  cnf(c_0_38, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_22]), c_0_22]), c_0_22]), c_0_22])).
% 0.12/0.40  cnf(c_0_39, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_22]), c_0_22])).
% 0.12/0.40  cnf(c_0_40, negated_conjecture, (k2_xboole_0(esk3_0,esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_31, c_0_35])).
% 0.12/0.40  cnf(c_0_41, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)!=k1_tarski(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.40  cnf(c_0_42, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0))))=k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39])).
% 0.12/0.40  cnf(c_0_43, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))=k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X1,X2))))), inference(spm,[status(thm)],[c_0_39, c_0_38])).
% 0.12/0.40  cnf(c_0_44, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))=esk3_0), inference(spm,[status(thm)],[c_0_36, c_0_40])).
% 0.12/0.40  cnf(c_0_45, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0))!=k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_18]), c_0_19]), c_0_20]), c_0_22])).
% 0.12/0.40  cnf(c_0_46, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))))=k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_39])).
% 0.12/0.40  cnf(c_0_47, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1))))=k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))), inference(spm,[status(thm)],[c_0_38, c_0_44])).
% 0.12/0.40  cnf(c_0_48, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))!=k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0))), inference(rw,[status(thm)],[c_0_45, c_0_27])).
% 0.12/0.40  cnf(c_0_49, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_48]), ['proof']).
% 0.12/0.40  # SZS output end CNFRefutation
% 0.12/0.40  # Proof object total steps             : 50
% 0.12/0.40  # Proof object clause steps            : 29
% 0.12/0.40  # Proof object formula steps           : 21
% 0.12/0.40  # Proof object conjectures             : 18
% 0.12/0.40  # Proof object clause conjectures      : 15
% 0.12/0.40  # Proof object formula conjectures     : 3
% 0.12/0.40  # Proof object initial clauses used    : 13
% 0.12/0.40  # Proof object initial formulas used   : 10
% 0.12/0.40  # Proof object generating inferences   : 7
% 0.12/0.40  # Proof object simplifying inferences  : 26
% 0.12/0.40  # Training examples: 0 positive, 0 negative
% 0.12/0.40  # Parsed axioms                        : 14
% 0.12/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.40  # Initial clauses                      : 27
% 0.12/0.40  # Removed in clause preprocessing      : 4
% 0.12/0.40  # Initial clauses in saturation        : 23
% 0.12/0.40  # Processed clauses                    : 336
% 0.12/0.40  # ...of these trivial                  : 8
% 0.12/0.40  # ...subsumed                          : 123
% 0.12/0.40  # ...remaining for further processing  : 205
% 0.12/0.40  # Other redundant clauses eliminated   : 5
% 0.12/0.40  # Clauses deleted for lack of memory   : 0
% 0.12/0.40  # Backward-subsumed                    : 2
% 0.12/0.40  # Backward-rewritten                   : 15
% 0.12/0.40  # Generated clauses                    : 1939
% 0.12/0.40  # ...of the previous two non-trivial   : 1542
% 0.12/0.40  # Contextual simplify-reflections      : 0
% 0.12/0.40  # Paramodulations                      : 1930
% 0.12/0.40  # Factorizations                       : 2
% 0.12/0.40  # Equation resolutions                 : 5
% 0.12/0.40  # Propositional unsat checks           : 0
% 0.12/0.40  #    Propositional check models        : 0
% 0.12/0.40  #    Propositional check unsatisfiable : 0
% 0.12/0.40  #    Propositional clauses             : 0
% 0.12/0.40  #    Propositional clauses after purity: 0
% 0.12/0.40  #    Propositional unsat core size     : 0
% 0.12/0.40  #    Propositional preprocessing time  : 0.000
% 0.12/0.40  #    Propositional encoding time       : 0.000
% 0.12/0.40  #    Propositional solver time         : 0.000
% 0.12/0.40  #    Success case prop preproc time    : 0.000
% 0.12/0.40  #    Success case prop encoding time   : 0.000
% 0.12/0.40  #    Success case prop solver time     : 0.000
% 0.12/0.40  # Current number of processed clauses  : 159
% 0.12/0.40  #    Positive orientable unit clauses  : 55
% 0.12/0.40  #    Positive unorientable unit clauses: 2
% 0.12/0.40  #    Negative unit clauses             : 20
% 0.12/0.40  #    Non-unit-clauses                  : 82
% 0.12/0.40  # Current number of unprocessed clauses: 1243
% 0.12/0.40  # ...number of literals in the above   : 1997
% 0.12/0.40  # Current number of archived formulas  : 0
% 0.12/0.40  # Current number of archived clauses   : 45
% 0.12/0.40  # Clause-clause subsumption calls (NU) : 654
% 0.12/0.40  # Rec. Clause-clause subsumption calls : 600
% 0.12/0.40  # Non-unit clause-clause subsumptions  : 78
% 0.12/0.40  # Unit Clause-clause subsumption calls : 127
% 0.12/0.40  # Rewrite failures with RHS unbound    : 0
% 0.12/0.40  # BW rewrite match attempts            : 242
% 0.12/0.40  # BW rewrite match successes           : 42
% 0.12/0.40  # Condensation attempts                : 0
% 0.12/0.40  # Condensation successes               : 0
% 0.12/0.40  # Termbank termtop insertions          : 45796
% 0.12/0.40  
% 0.12/0.40  # -------------------------------------------------
% 0.12/0.40  # User time                : 0.051 s
% 0.12/0.40  # System time              : 0.008 s
% 0.12/0.40  # Total time               : 0.059 s
% 0.12/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
