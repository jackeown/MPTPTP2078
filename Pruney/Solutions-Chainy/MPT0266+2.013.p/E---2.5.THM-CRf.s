%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:42:11 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   34 (  61 expanded)
%              Number of clauses        :   17 (  25 expanded)
%              Number of leaves         :    8 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :   90 ( 120 expanded)
%              Number of equality atoms :   51 (  78 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t63_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k3_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
     => r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_zfmisc_1)).

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

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k3_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
       => r2_hidden(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t63_zfmisc_1])).

fof(c_0_9,negated_conjecture,
    ( k3_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k2_tarski(esk3_0,esk4_0)
    & ~ r2_hidden(esk3_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_10,plain,(
    ! [X26,X27] : k1_enumset1(X26,X26,X27) = k2_tarski(X26,X27) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_11,plain,(
    ! [X28,X29,X30] : k2_enumset1(X28,X28,X29,X30) = k1_enumset1(X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_12,plain,(
    ! [X31,X32,X33,X34] : k3_enumset1(X31,X31,X32,X33,X34) = k2_enumset1(X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_13,plain,(
    ! [X35,X36,X37,X38,X39] : k4_enumset1(X35,X35,X36,X37,X38,X39) = k3_enumset1(X35,X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_14,plain,(
    ! [X17,X18,X19,X20,X21,X22,X23,X24] :
      ( ( ~ r2_hidden(X20,X19)
        | X20 = X17
        | X20 = X18
        | X19 != k2_tarski(X17,X18) )
      & ( X21 != X17
        | r2_hidden(X21,X19)
        | X19 != k2_tarski(X17,X18) )
      & ( X21 != X18
        | r2_hidden(X21,X19)
        | X19 != k2_tarski(X17,X18) )
      & ( esk2_3(X22,X23,X24) != X22
        | ~ r2_hidden(esk2_3(X22,X23,X24),X24)
        | X24 = k2_tarski(X22,X23) )
      & ( esk2_3(X22,X23,X24) != X23
        | ~ r2_hidden(esk2_3(X22,X23,X24),X24)
        | X24 = k2_tarski(X22,X23) )
      & ( r2_hidden(esk2_3(X22,X23,X24),X24)
        | esk2_3(X22,X23,X24) = X22
        | esk2_3(X22,X23,X24) = X23
        | X24 = k2_tarski(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_15,plain,(
    ! [X8,X9,X10,X11,X12,X13,X14,X15] :
      ( ( r2_hidden(X11,X8)
        | ~ r2_hidden(X11,X10)
        | X10 != k3_xboole_0(X8,X9) )
      & ( r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | X10 != k3_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X12,X8)
        | ~ r2_hidden(X12,X9)
        | r2_hidden(X12,X10)
        | X10 != k3_xboole_0(X8,X9) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X13)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X14)
        | X15 = k3_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X13)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k3_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X14)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k3_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_16,negated_conjecture,
    ( k3_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k2_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( k3_xboole_0(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0) = k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_17]),c_0_18]),c_0_18]),c_0_19]),c_0_19]),c_0_20]),c_0_20])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X2,X2,X2,X2,X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( k3_xboole_0(esk5_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | X2 != k4_enumset1(X1,X1,X1,X1,X1,X3) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k4_enumset1(X1,X1,X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:15:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.20/0.39  # and selection function SelectNegativeLiterals.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.038 s
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t63_zfmisc_1, conjecture, ![X1, X2, X3]:(k3_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)=>r2_hidden(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 0.20/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.39  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.20/0.39  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.20/0.39  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.39  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3]:(k3_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)=>r2_hidden(X1,X3))), inference(assume_negation,[status(cth)],[t63_zfmisc_1])).
% 0.20/0.39  fof(c_0_9, negated_conjecture, (k3_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k2_tarski(esk3_0,esk4_0)&~r2_hidden(esk3_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.20/0.39  fof(c_0_10, plain, ![X26, X27]:k1_enumset1(X26,X26,X27)=k2_tarski(X26,X27), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.39  fof(c_0_11, plain, ![X28, X29, X30]:k2_enumset1(X28,X28,X29,X30)=k1_enumset1(X28,X29,X30), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.39  fof(c_0_12, plain, ![X31, X32, X33, X34]:k3_enumset1(X31,X31,X32,X33,X34)=k2_enumset1(X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.39  fof(c_0_13, plain, ![X35, X36, X37, X38, X39]:k4_enumset1(X35,X35,X36,X37,X38,X39)=k3_enumset1(X35,X36,X37,X38,X39), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.39  fof(c_0_14, plain, ![X17, X18, X19, X20, X21, X22, X23, X24]:(((~r2_hidden(X20,X19)|(X20=X17|X20=X18)|X19!=k2_tarski(X17,X18))&((X21!=X17|r2_hidden(X21,X19)|X19!=k2_tarski(X17,X18))&(X21!=X18|r2_hidden(X21,X19)|X19!=k2_tarski(X17,X18))))&(((esk2_3(X22,X23,X24)!=X22|~r2_hidden(esk2_3(X22,X23,X24),X24)|X24=k2_tarski(X22,X23))&(esk2_3(X22,X23,X24)!=X23|~r2_hidden(esk2_3(X22,X23,X24),X24)|X24=k2_tarski(X22,X23)))&(r2_hidden(esk2_3(X22,X23,X24),X24)|(esk2_3(X22,X23,X24)=X22|esk2_3(X22,X23,X24)=X23)|X24=k2_tarski(X22,X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.20/0.39  fof(c_0_15, plain, ![X8, X9, X10, X11, X12, X13, X14, X15]:((((r2_hidden(X11,X8)|~r2_hidden(X11,X10)|X10!=k3_xboole_0(X8,X9))&(r2_hidden(X11,X9)|~r2_hidden(X11,X10)|X10!=k3_xboole_0(X8,X9)))&(~r2_hidden(X12,X8)|~r2_hidden(X12,X9)|r2_hidden(X12,X10)|X10!=k3_xboole_0(X8,X9)))&((~r2_hidden(esk1_3(X13,X14,X15),X15)|(~r2_hidden(esk1_3(X13,X14,X15),X13)|~r2_hidden(esk1_3(X13,X14,X15),X14))|X15=k3_xboole_0(X13,X14))&((r2_hidden(esk1_3(X13,X14,X15),X13)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k3_xboole_0(X13,X14))&(r2_hidden(esk1_3(X13,X14,X15),X14)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k3_xboole_0(X13,X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.20/0.39  cnf(c_0_16, negated_conjecture, (k3_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k2_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_18, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_19, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_20, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  fof(c_0_21, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.39  cnf(c_0_22, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.39  cnf(c_0_23, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_24, negated_conjecture, (k3_xboole_0(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)=k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_17]), c_0_18]), c_0_18]), c_0_19]), c_0_19]), c_0_20]), c_0_20])).
% 0.20/0.39  cnf(c_0_25, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.39  cnf(c_0_26, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X2,X2,X2,X2,X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 0.20/0.39  cnf(c_0_27, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_23])).
% 0.20/0.39  cnf(c_0_28, negated_conjecture, (k3_xboole_0(esk5_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.39  cnf(c_0_29, plain, (r2_hidden(X1,X2)|X2!=k4_enumset1(X1,X1,X1,X1,X1,X3)), inference(er,[status(thm)],[c_0_26])).
% 0.20/0.39  cnf(c_0_30, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.39  cnf(c_0_31, plain, (r2_hidden(X1,k4_enumset1(X1,X1,X1,X1,X1,X2))), inference(er,[status(thm)],[c_0_29])).
% 0.20/0.39  cnf(c_0_32, negated_conjecture, (~r2_hidden(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_33, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 34
% 0.20/0.39  # Proof object clause steps            : 17
% 0.20/0.39  # Proof object formula steps           : 17
% 0.20/0.39  # Proof object conjectures             : 9
% 0.20/0.39  # Proof object clause conjectures      : 6
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 9
% 0.20/0.39  # Proof object initial formulas used   : 8
% 0.20/0.39  # Proof object generating inferences   : 4
% 0.20/0.39  # Proof object simplifying inferences  : 15
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 8
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 19
% 0.20/0.39  # Removed in clause preprocessing      : 4
% 0.20/0.39  # Initial clauses in saturation        : 15
% 0.20/0.39  # Processed clauses                    : 56
% 0.20/0.39  # ...of these trivial                  : 2
% 0.20/0.39  # ...subsumed                          : 16
% 0.20/0.39  # ...remaining for further processing  : 38
% 0.20/0.39  # Other redundant clauses eliminated   : 11
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 1
% 0.20/0.39  # Generated clauses                    : 252
% 0.20/0.39  # ...of the previous two non-trivial   : 217
% 0.20/0.39  # Contextual simplify-reflections      : 2
% 0.20/0.39  # Paramodulations                      : 228
% 0.20/0.39  # Factorizations                       : 4
% 0.20/0.39  # Equation resolutions                 : 20
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 35
% 0.20/0.39  #    Positive orientable unit clauses  : 5
% 0.20/0.39  #    Positive unorientable unit clauses: 1
% 0.20/0.39  #    Negative unit clauses             : 1
% 0.20/0.39  #    Non-unit-clauses                  : 28
% 0.20/0.39  # Current number of unprocessed clauses: 166
% 0.20/0.39  # ...number of literals in the above   : 684
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 5
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 135
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 112
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 18
% 0.20/0.39  # Unit Clause-clause subsumption calls : 12
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 15
% 0.20/0.39  # BW rewrite match successes           : 2
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 4187
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.045 s
% 0.20/0.40  # System time              : 0.007 s
% 0.20/0.40  # Total time               : 0.051 s
% 0.20/0.40  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
