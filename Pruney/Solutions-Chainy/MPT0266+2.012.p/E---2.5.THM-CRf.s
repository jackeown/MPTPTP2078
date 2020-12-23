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
% DateTime   : Thu Dec  3 10:42:11 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 (  71 expanded)
%              Number of clauses        :   21 (  29 expanded)
%              Number of leaves         :   11 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :  100 ( 130 expanded)
%              Number of equality atoms :   61 (  88 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t63_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k3_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
     => r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_zfmisc_1)).

fof(t24_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k3_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
       => r2_hidden(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t63_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X20,X21,X22] : k2_xboole_0(X20,k3_xboole_0(X21,X22)) = k3_xboole_0(k2_xboole_0(X20,X21),k2_xboole_0(X20,X22)) ),
    inference(variable_rename,[status(thm)],[t24_xboole_1])).

fof(c_0_13,plain,(
    ! [X17] : k2_xboole_0(X17,X17) = X17 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_14,plain,(
    ! [X18,X19] : k3_xboole_0(X18,k2_xboole_0(X18,X19)) = X18 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

fof(c_0_15,negated_conjecture,
    ( k3_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k2_tarski(esk3_0,esk4_0)
    & ~ r2_hidden(esk3_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_16,plain,(
    ! [X32,X33] : k1_enumset1(X32,X32,X33) = k2_tarski(X32,X33) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X34,X35,X36] : k2_enumset1(X34,X34,X35,X36) = k1_enumset1(X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_18,plain,(
    ! [X37,X38,X39,X40] : k3_enumset1(X37,X37,X38,X39,X40) = k2_enumset1(X37,X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_19,plain,(
    ! [X41,X42,X43,X44,X45] : k4_enumset1(X41,X41,X42,X43,X44,X45) = k3_enumset1(X41,X42,X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_20,plain,(
    ! [X23,X24,X25,X26,X27,X28,X29,X30] :
      ( ( ~ r2_hidden(X26,X25)
        | X26 = X23
        | X26 = X24
        | X25 != k2_tarski(X23,X24) )
      & ( X27 != X23
        | r2_hidden(X27,X25)
        | X25 != k2_tarski(X23,X24) )
      & ( X27 != X24
        | r2_hidden(X27,X25)
        | X25 != k2_tarski(X23,X24) )
      & ( esk2_3(X28,X29,X30) != X28
        | ~ r2_hidden(esk2_3(X28,X29,X30),X30)
        | X30 = k2_tarski(X28,X29) )
      & ( esk2_3(X28,X29,X30) != X29
        | ~ r2_hidden(esk2_3(X28,X29,X30),X30)
        | X30 = k2_tarski(X28,X29) )
      & ( r2_hidden(esk2_3(X28,X29,X30),X30)
        | esk2_3(X28,X29,X30) = X28
        | esk2_3(X28,X29,X30) = X29
        | X30 = k2_tarski(X28,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_21,plain,(
    ! [X8,X9,X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X11,X10)
        | r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X10 != k2_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X12,X8)
        | r2_hidden(X12,X10)
        | X10 != k2_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X12,X9)
        | r2_hidden(X12,X10)
        | X10 != k2_xboole_0(X8,X9) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X13)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X14)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k2_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X15)
        | r2_hidden(esk1_3(X13,X14,X15),X13)
        | r2_hidden(esk1_3(X13,X14,X15),X14)
        | X15 = k2_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( k3_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k2_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_30,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( k3_xboole_0(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0) = k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_29]),c_0_29])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X2,X2,X2,X2,X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_26]),c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33])])).

cnf(c_0_38,negated_conjecture,
    ( k3_xboole_0(esk5_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | X2 != k4_enumset1(X1,X1,X1,X1,X1,X3) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k4_enumset1(X1,X1,X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:48:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.51  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.20/0.51  # and selection function SelectNegativeLiterals.
% 0.20/0.51  #
% 0.20/0.51  # Preprocessing time       : 0.027 s
% 0.20/0.51  
% 0.20/0.51  # Proof found!
% 0.20/0.51  # SZS status Theorem
% 0.20/0.51  # SZS output start CNFRefutation
% 0.20/0.51  fof(t63_zfmisc_1, conjecture, ![X1, X2, X3]:(k3_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)=>r2_hidden(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 0.20/0.51  fof(t24_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_xboole_1)).
% 0.20/0.51  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.20/0.51  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.20/0.51  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.51  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.51  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.51  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.51  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.20/0.51  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.20/0.51  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.51  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3]:(k3_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)=>r2_hidden(X1,X3))), inference(assume_negation,[status(cth)],[t63_zfmisc_1])).
% 0.20/0.51  fof(c_0_12, plain, ![X20, X21, X22]:k2_xboole_0(X20,k3_xboole_0(X21,X22))=k3_xboole_0(k2_xboole_0(X20,X21),k2_xboole_0(X20,X22)), inference(variable_rename,[status(thm)],[t24_xboole_1])).
% 0.20/0.51  fof(c_0_13, plain, ![X17]:k2_xboole_0(X17,X17)=X17, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.20/0.51  fof(c_0_14, plain, ![X18, X19]:k3_xboole_0(X18,k2_xboole_0(X18,X19))=X18, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.20/0.51  fof(c_0_15, negated_conjecture, (k3_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k2_tarski(esk3_0,esk4_0)&~r2_hidden(esk3_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.20/0.51  fof(c_0_16, plain, ![X32, X33]:k1_enumset1(X32,X32,X33)=k2_tarski(X32,X33), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.51  fof(c_0_17, plain, ![X34, X35, X36]:k2_enumset1(X34,X34,X35,X36)=k1_enumset1(X34,X35,X36), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.51  fof(c_0_18, plain, ![X37, X38, X39, X40]:k3_enumset1(X37,X37,X38,X39,X40)=k2_enumset1(X37,X38,X39,X40), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.51  fof(c_0_19, plain, ![X41, X42, X43, X44, X45]:k4_enumset1(X41,X41,X42,X43,X44,X45)=k3_enumset1(X41,X42,X43,X44,X45), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.51  fof(c_0_20, plain, ![X23, X24, X25, X26, X27, X28, X29, X30]:(((~r2_hidden(X26,X25)|(X26=X23|X26=X24)|X25!=k2_tarski(X23,X24))&((X27!=X23|r2_hidden(X27,X25)|X25!=k2_tarski(X23,X24))&(X27!=X24|r2_hidden(X27,X25)|X25!=k2_tarski(X23,X24))))&(((esk2_3(X28,X29,X30)!=X28|~r2_hidden(esk2_3(X28,X29,X30),X30)|X30=k2_tarski(X28,X29))&(esk2_3(X28,X29,X30)!=X29|~r2_hidden(esk2_3(X28,X29,X30),X30)|X30=k2_tarski(X28,X29)))&(r2_hidden(esk2_3(X28,X29,X30),X30)|(esk2_3(X28,X29,X30)=X28|esk2_3(X28,X29,X30)=X29)|X30=k2_tarski(X28,X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.20/0.51  fof(c_0_21, plain, ![X8, X9, X10, X11, X12, X13, X14, X15]:(((~r2_hidden(X11,X10)|(r2_hidden(X11,X8)|r2_hidden(X11,X9))|X10!=k2_xboole_0(X8,X9))&((~r2_hidden(X12,X8)|r2_hidden(X12,X10)|X10!=k2_xboole_0(X8,X9))&(~r2_hidden(X12,X9)|r2_hidden(X12,X10)|X10!=k2_xboole_0(X8,X9))))&(((~r2_hidden(esk1_3(X13,X14,X15),X13)|~r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k2_xboole_0(X13,X14))&(~r2_hidden(esk1_3(X13,X14,X15),X14)|~r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k2_xboole_0(X13,X14)))&(r2_hidden(esk1_3(X13,X14,X15),X15)|(r2_hidden(esk1_3(X13,X14,X15),X13)|r2_hidden(esk1_3(X13,X14,X15),X14))|X15=k2_xboole_0(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.20/0.51  cnf(c_0_22, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.51  cnf(c_0_23, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.51  cnf(c_0_24, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.51  cnf(c_0_25, negated_conjecture, (k3_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k2_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.51  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.51  cnf(c_0_27, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.51  cnf(c_0_28, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.51  cnf(c_0_29, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.51  fof(c_0_30, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.51  cnf(c_0_31, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.51  cnf(c_0_32, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.51  cnf(c_0_33, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 0.20/0.51  cnf(c_0_34, negated_conjecture, (k3_xboole_0(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)=k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_29]), c_0_29])).
% 0.20/0.51  cnf(c_0_35, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.51  cnf(c_0_36, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X2,X2,X2,X2,X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_26]), c_0_27]), c_0_28]), c_0_29])).
% 0.20/0.51  cnf(c_0_37, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33])])).
% 0.20/0.51  cnf(c_0_38, negated_conjecture, (k3_xboole_0(esk5_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.51  cnf(c_0_39, plain, (r2_hidden(X1,X2)|X2!=k4_enumset1(X1,X1,X1,X1,X1,X3)), inference(er,[status(thm)],[c_0_36])).
% 0.20/0.51  cnf(c_0_40, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.51  cnf(c_0_41, plain, (r2_hidden(X1,k4_enumset1(X1,X1,X1,X1,X1,X2))), inference(er,[status(thm)],[c_0_39])).
% 0.20/0.51  cnf(c_0_42, negated_conjecture, (~r2_hidden(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.51  cnf(c_0_43, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), ['proof']).
% 0.20/0.51  # SZS output end CNFRefutation
% 0.20/0.51  # Proof object total steps             : 44
% 0.20/0.51  # Proof object clause steps            : 21
% 0.20/0.51  # Proof object formula steps           : 23
% 0.20/0.51  # Proof object conjectures             : 9
% 0.20/0.51  # Proof object clause conjectures      : 6
% 0.20/0.51  # Proof object formula conjectures     : 3
% 0.20/0.51  # Proof object initial clauses used    : 12
% 0.20/0.51  # Proof object initial formulas used   : 11
% 0.20/0.51  # Proof object generating inferences   : 5
% 0.20/0.51  # Proof object simplifying inferences  : 17
% 0.20/0.51  # Training examples: 0 positive, 0 negative
% 0.20/0.51  # Parsed axioms                        : 11
% 0.20/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.51  # Initial clauses                      : 22
% 0.20/0.51  # Removed in clause preprocessing      : 4
% 0.20/0.51  # Initial clauses in saturation        : 18
% 0.20/0.51  # Processed clauses                    : 578
% 0.20/0.51  # ...of these trivial                  : 58
% 0.20/0.51  # ...subsumed                          : 370
% 0.20/0.51  # ...remaining for further processing  : 150
% 0.20/0.51  # Other redundant clauses eliminated   : 377
% 0.20/0.51  # Clauses deleted for lack of memory   : 0
% 0.20/0.51  # Backward-subsumed                    : 0
% 0.20/0.51  # Backward-rewritten                   : 1
% 0.20/0.51  # Generated clauses                    : 6218
% 0.20/0.51  # ...of the previous two non-trivial   : 5270
% 0.20/0.51  # Contextual simplify-reflections      : 0
% 0.20/0.51  # Paramodulations                      : 5766
% 0.20/0.51  # Factorizations                       : 34
% 0.20/0.51  # Equation resolutions                 : 418
% 0.20/0.51  # Propositional unsat checks           : 0
% 0.20/0.51  #    Propositional check models        : 0
% 0.20/0.51  #    Propositional check unsatisfiable : 0
% 0.20/0.51  #    Propositional clauses             : 0
% 0.20/0.51  #    Propositional clauses after purity: 0
% 0.20/0.51  #    Propositional unsat core size     : 0
% 0.20/0.51  #    Propositional preprocessing time  : 0.000
% 0.20/0.51  #    Propositional encoding time       : 0.000
% 0.20/0.51  #    Propositional solver time         : 0.000
% 0.20/0.51  #    Success case prop preproc time    : 0.000
% 0.20/0.51  #    Success case prop encoding time   : 0.000
% 0.20/0.51  #    Success case prop solver time     : 0.000
% 0.20/0.51  # Current number of processed clauses  : 147
% 0.20/0.51  #    Positive orientable unit clauses  : 40
% 0.20/0.51  #    Positive unorientable unit clauses: 1
% 0.20/0.51  #    Negative unit clauses             : 1
% 0.20/0.51  #    Non-unit-clauses                  : 105
% 0.20/0.51  # Current number of unprocessed clauses: 4691
% 0.20/0.51  # ...number of literals in the above   : 30530
% 0.20/0.51  # Current number of archived formulas  : 0
% 0.20/0.51  # Current number of archived clauses   : 5
% 0.20/0.51  # Clause-clause subsumption calls (NU) : 7686
% 0.20/0.51  # Rec. Clause-clause subsumption calls : 4238
% 0.20/0.51  # Non-unit clause-clause subsumptions  : 368
% 0.20/0.51  # Unit Clause-clause subsumption calls : 31
% 0.20/0.51  # Rewrite failures with RHS unbound    : 0
% 0.20/0.51  # BW rewrite match attempts            : 85
% 0.20/0.51  # BW rewrite match successes           : 2
% 0.20/0.51  # Condensation attempts                : 0
% 0.20/0.51  # Condensation successes               : 0
% 0.20/0.51  # Termbank termtop insertions          : 114715
% 0.20/0.51  
% 0.20/0.51  # -------------------------------------------------
% 0.20/0.51  # User time                : 0.160 s
% 0.20/0.51  # System time              : 0.009 s
% 0.20/0.51  # Total time               : 0.169 s
% 0.20/0.51  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
