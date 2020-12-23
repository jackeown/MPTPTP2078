%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:32 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 448 expanded)
%              Number of clauses        :   32 ( 178 expanded)
%              Number of leaves         :   10 ( 126 expanded)
%              Depth                    :   15
%              Number of atoms          :  135 ( 797 expanded)
%              Number of equality atoms :   64 ( 541 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t39_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(X1,k1_tarski(X2))
      <=> ( X1 = k1_xboole_0
          | X1 = k1_tarski(X2) ) ) ),
    inference(assume_negation,[status(cth)],[t39_zfmisc_1])).

fof(c_0_11,negated_conjecture,
    ( ( esk4_0 != k1_xboole_0
      | ~ r1_tarski(esk4_0,k1_tarski(esk5_0)) )
    & ( esk4_0 != k1_tarski(esk5_0)
      | ~ r1_tarski(esk4_0,k1_tarski(esk5_0)) )
    & ( r1_tarski(esk4_0,k1_tarski(esk5_0))
      | esk4_0 = k1_xboole_0
      | esk4_0 = k1_tarski(esk5_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).

fof(c_0_12,plain,(
    ! [X25] : k2_tarski(X25,X25) = k1_tarski(X25) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_13,plain,(
    ! [X26,X27] : k1_enumset1(X26,X26,X27) = k2_tarski(X26,X27) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X28,X29,X30] : k2_enumset1(X28,X28,X29,X30) = k1_enumset1(X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_15,negated_conjecture,
    ( esk4_0 != k1_tarski(esk5_0)
    | ~ r1_tarski(esk4_0,k1_tarski(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk4_0,k1_tarski(esk5_0))
    | esk4_0 = k1_xboole_0
    | esk4_0 = k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_20,plain,(
    ! [X13,X14] :
      ( ( r1_tarski(X13,X14)
        | X13 != X14 )
      & ( r1_tarski(X14,X13)
        | X13 != X14 )
      & ( ~ r1_tarski(X13,X14)
        | ~ r1_tarski(X14,X13)
        | X13 = X14 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_21,negated_conjecture,
    ( esk4_0 != k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)
    | ~ r1_tarski(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_16]),c_0_17]),c_0_17]),c_0_18]),c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk4_0 = k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)
    | r1_tarski(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_16]),c_0_16]),c_0_17]),c_0_17]),c_0_18]),c_0_18])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    | ~ r1_tarski(esk4_0,k1_tarski(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))
    | ~ r1_tarski(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X15] : r1_tarski(k1_xboole_0,X15) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_28,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    | ~ r1_tarski(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26])])).

cnf(c_0_30,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

fof(c_0_32,plain,(
    ! [X11] :
      ( X11 = k1_xboole_0
      | r2_hidden(esk2_1(X11),X11) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_33,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22,X23] :
      ( ( ~ r2_hidden(X19,X18)
        | X19 = X16
        | X19 = X17
        | X18 != k2_tarski(X16,X17) )
      & ( X20 != X16
        | r2_hidden(X20,X18)
        | X18 != k2_tarski(X16,X17) )
      & ( X20 != X17
        | r2_hidden(X20,X18)
        | X18 != k2_tarski(X16,X17) )
      & ( esk3_3(X21,X22,X23) != X21
        | ~ r2_hidden(esk3_3(X21,X22,X23),X23)
        | X23 = k2_tarski(X21,X22) )
      & ( esk3_3(X21,X22,X23) != X22
        | ~ r2_hidden(esk3_3(X21,X22,X23),X23)
        | X23 = k2_tarski(X21,X22) )
      & ( r2_hidden(esk3_3(X21,X22,X23),X23)
        | esk3_3(X21,X22,X23) = X21
        | esk3_3(X21,X22,X23) = X22
        | X23 = k2_tarski(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_34,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_35,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_31])])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_17]),c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),X1)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_42,plain,(
    ! [X31,X32] :
      ( ( ~ r1_tarski(k1_tarski(X31),X32)
        | r2_hidden(X31,X32) )
      & ( ~ r2_hidden(X31,X32)
        | r1_tarski(k1_tarski(X31),X32) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_43,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_enumset1(X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_31])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( esk2_1(esk4_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_47,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_39,c_0_46])).

cnf(c_0_49,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_31])])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_31])]),c_0_51]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:33:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.21/0.39  # and selection function SelectNegativeLiterals.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.038 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(t39_zfmisc_1, conjecture, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 0.21/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.21/0.39  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.21/0.39  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.21/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.39  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.21/0.39  fof(c_0_10, negated_conjecture, ~(![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2)))), inference(assume_negation,[status(cth)],[t39_zfmisc_1])).
% 0.21/0.39  fof(c_0_11, negated_conjecture, (((esk4_0!=k1_xboole_0|~r1_tarski(esk4_0,k1_tarski(esk5_0)))&(esk4_0!=k1_tarski(esk5_0)|~r1_tarski(esk4_0,k1_tarski(esk5_0))))&(r1_tarski(esk4_0,k1_tarski(esk5_0))|(esk4_0=k1_xboole_0|esk4_0=k1_tarski(esk5_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).
% 0.21/0.39  fof(c_0_12, plain, ![X25]:k2_tarski(X25,X25)=k1_tarski(X25), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.39  fof(c_0_13, plain, ![X26, X27]:k1_enumset1(X26,X26,X27)=k2_tarski(X26,X27), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.39  fof(c_0_14, plain, ![X28, X29, X30]:k2_enumset1(X28,X28,X29,X30)=k1_enumset1(X28,X29,X30), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.39  cnf(c_0_15, negated_conjecture, (esk4_0!=k1_tarski(esk5_0)|~r1_tarski(esk4_0,k1_tarski(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.39  cnf(c_0_16, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.39  cnf(c_0_18, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_19, negated_conjecture, (r1_tarski(esk4_0,k1_tarski(esk5_0))|esk4_0=k1_xboole_0|esk4_0=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.39  fof(c_0_20, plain, ![X13, X14]:(((r1_tarski(X13,X14)|X13!=X14)&(r1_tarski(X14,X13)|X13!=X14))&(~r1_tarski(X13,X14)|~r1_tarski(X14,X13)|X13=X14)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.39  cnf(c_0_21, negated_conjecture, (esk4_0!=k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)|~r1_tarski(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_16]), c_0_17]), c_0_17]), c_0_18]), c_0_18])).
% 0.21/0.39  cnf(c_0_22, negated_conjecture, (esk4_0=k1_xboole_0|esk4_0=k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)|r1_tarski(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_16]), c_0_16]), c_0_17]), c_0_17]), c_0_18]), c_0_18])).
% 0.21/0.39  cnf(c_0_23, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.39  cnf(c_0_24, negated_conjecture, (esk4_0!=k1_xboole_0|~r1_tarski(esk4_0,k1_tarski(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.39  cnf(c_0_25, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))|~r1_tarski(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.21/0.39  cnf(c_0_26, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_23])).
% 0.21/0.39  fof(c_0_27, plain, ![X15]:r1_tarski(k1_xboole_0,X15), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.21/0.39  cnf(c_0_28, negated_conjecture, (esk4_0!=k1_xboole_0|~r1_tarski(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_16]), c_0_17]), c_0_18])).
% 0.21/0.39  cnf(c_0_29, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26])])).
% 0.21/0.39  cnf(c_0_30, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.39  cnf(c_0_31, negated_conjecture, (r1_tarski(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])])).
% 0.21/0.39  fof(c_0_32, plain, ![X11]:(X11=k1_xboole_0|r2_hidden(esk2_1(X11),X11)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.21/0.39  fof(c_0_33, plain, ![X16, X17, X18, X19, X20, X21, X22, X23]:(((~r2_hidden(X19,X18)|(X19=X16|X19=X17)|X18!=k2_tarski(X16,X17))&((X20!=X16|r2_hidden(X20,X18)|X18!=k2_tarski(X16,X17))&(X20!=X17|r2_hidden(X20,X18)|X18!=k2_tarski(X16,X17))))&(((esk3_3(X21,X22,X23)!=X21|~r2_hidden(esk3_3(X21,X22,X23),X23)|X23=k2_tarski(X21,X22))&(esk3_3(X21,X22,X23)!=X22|~r2_hidden(esk3_3(X21,X22,X23),X23)|X23=k2_tarski(X21,X22)))&(r2_hidden(esk3_3(X21,X22,X23),X23)|(esk3_3(X21,X22,X23)=X21|esk3_3(X21,X22,X23)=X22)|X23=k2_tarski(X21,X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.21/0.39  fof(c_0_34, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.39  cnf(c_0_35, negated_conjecture, (esk4_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_31])])).
% 0.21/0.39  cnf(c_0_36, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.39  cnf(c_0_37, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.39  cnf(c_0_38, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.39  cnf(c_0_39, negated_conjecture, (r2_hidden(esk2_1(esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.21/0.39  cnf(c_0_40, plain, (X1=X4|X1=X3|X2!=k2_enumset1(X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_17]), c_0_18])).
% 0.21/0.39  cnf(c_0_41, negated_conjecture, (r2_hidden(esk2_1(esk4_0),X1)|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.21/0.39  fof(c_0_42, plain, ![X31, X32]:((~r1_tarski(k1_tarski(X31),X32)|r2_hidden(X31,X32))&(~r2_hidden(X31,X32)|r1_tarski(k1_tarski(X31),X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.21/0.39  cnf(c_0_43, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_enumset1(X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_40])).
% 0.21/0.39  cnf(c_0_44, negated_conjecture, (r2_hidden(esk2_1(esk4_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_41, c_0_31])).
% 0.21/0.39  cnf(c_0_45, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.39  cnf(c_0_46, negated_conjecture, (esk2_1(esk4_0)=esk5_0), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.21/0.39  cnf(c_0_47, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_16]), c_0_17]), c_0_18])).
% 0.21/0.39  cnf(c_0_48, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(rw,[status(thm)],[c_0_39, c_0_46])).
% 0.21/0.39  cnf(c_0_49, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.39  cnf(c_0_50, negated_conjecture, (r1_tarski(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.21/0.39  cnf(c_0_51, negated_conjecture, (k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_31])])).
% 0.21/0.39  cnf(c_0_52, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_31])]), c_0_51]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 53
% 0.21/0.39  # Proof object clause steps            : 32
% 0.21/0.39  # Proof object formula steps           : 21
% 0.21/0.39  # Proof object conjectures             : 21
% 0.21/0.39  # Proof object clause conjectures      : 18
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 13
% 0.21/0.39  # Proof object initial formulas used   : 10
% 0.21/0.39  # Proof object generating inferences   : 8
% 0.21/0.39  # Proof object simplifying inferences  : 34
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 10
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 22
% 0.21/0.39  # Removed in clause preprocessing      : 3
% 0.21/0.39  # Initial clauses in saturation        : 19
% 0.21/0.39  # Processed clauses                    : 57
% 0.21/0.39  # ...of these trivial                  : 1
% 0.21/0.39  # ...subsumed                          : 3
% 0.21/0.39  # ...remaining for further processing  : 53
% 0.21/0.39  # Other redundant clauses eliminated   : 7
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 1
% 0.21/0.39  # Backward-rewritten                   : 7
% 0.21/0.39  # Generated clauses                    : 86
% 0.21/0.39  # ...of the previous two non-trivial   : 70
% 0.21/0.39  # Contextual simplify-reflections      : 0
% 0.21/0.39  # Paramodulations                      : 81
% 0.21/0.39  # Factorizations                       : 0
% 0.21/0.39  # Equation resolutions                 : 7
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 22
% 0.21/0.39  #    Positive orientable unit clauses  : 8
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 2
% 0.21/0.39  #    Non-unit-clauses                  : 12
% 0.21/0.39  # Current number of unprocessed clauses: 49
% 0.21/0.39  # ...number of literals in the above   : 119
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 29
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 21
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 20
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 3
% 0.21/0.39  # Unit Clause-clause subsumption calls : 7
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 10
% 0.21/0.39  # BW rewrite match successes           : 3
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 2029
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.040 s
% 0.21/0.39  # System time              : 0.006 s
% 0.21/0.39  # Total time               : 0.046 s
% 0.21/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
