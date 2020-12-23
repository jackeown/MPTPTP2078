%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:17 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 819 expanded)
%              Number of clauses        :   28 ( 346 expanded)
%              Number of leaves         :    6 ( 221 expanded)
%              Depth                    :   14
%              Number of atoms          :  134 (2374 expanded)
%              Number of equality atoms :  114 (2024 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   36 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( X5 = k2_enumset1(X1,X2,X3,X4)
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X6 != X1
              & X6 != X2
              & X6 != X3
              & X6 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

fof(t146_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t19_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k2_tarski(X4,X5)))
     => ( ( k1_mcart_1(X1) = X2
          | k1_mcart_1(X1) = X3 )
        & ( k2_mcart_1(X1) = X4
          | k2_mcart_1(X1) = X5 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_mcart_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(c_0_6,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( ~ r2_hidden(X21,X20)
        | X21 = X16
        | X21 = X17
        | X21 = X18
        | X21 = X19
        | X20 != k2_enumset1(X16,X17,X18,X19) )
      & ( X22 != X16
        | r2_hidden(X22,X20)
        | X20 != k2_enumset1(X16,X17,X18,X19) )
      & ( X22 != X17
        | r2_hidden(X22,X20)
        | X20 != k2_enumset1(X16,X17,X18,X19) )
      & ( X22 != X18
        | r2_hidden(X22,X20)
        | X20 != k2_enumset1(X16,X17,X18,X19) )
      & ( X22 != X19
        | r2_hidden(X22,X20)
        | X20 != k2_enumset1(X16,X17,X18,X19) )
      & ( esk1_5(X23,X24,X25,X26,X27) != X23
        | ~ r2_hidden(esk1_5(X23,X24,X25,X26,X27),X27)
        | X27 = k2_enumset1(X23,X24,X25,X26) )
      & ( esk1_5(X23,X24,X25,X26,X27) != X24
        | ~ r2_hidden(esk1_5(X23,X24,X25,X26,X27),X27)
        | X27 = k2_enumset1(X23,X24,X25,X26) )
      & ( esk1_5(X23,X24,X25,X26,X27) != X25
        | ~ r2_hidden(esk1_5(X23,X24,X25,X26,X27),X27)
        | X27 = k2_enumset1(X23,X24,X25,X26) )
      & ( esk1_5(X23,X24,X25,X26,X27) != X26
        | ~ r2_hidden(esk1_5(X23,X24,X25,X26,X27),X27)
        | X27 = k2_enumset1(X23,X24,X25,X26) )
      & ( r2_hidden(esk1_5(X23,X24,X25,X26,X27),X27)
        | esk1_5(X23,X24,X25,X26,X27) = X23
        | esk1_5(X23,X24,X25,X26,X27) = X24
        | esk1_5(X23,X24,X25,X26,X27) = X25
        | esk1_5(X23,X24,X25,X26,X27) = X26
        | X27 = k2_enumset1(X23,X24,X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_enumset1])])])])])])).

fof(c_0_7,plain,(
    ! [X12,X13,X14,X15] : k2_zfmisc_1(k2_tarski(X12,X13),k2_tarski(X14,X15)) = k2_enumset1(k4_tarski(X12,X14),k4_tarski(X12,X15),k4_tarski(X13,X14),k4_tarski(X13,X15)) ),
    inference(variable_rename,[status(thm)],[t146_zfmisc_1])).

fof(c_0_8,plain,(
    ! [X7,X8] : k1_enumset1(X7,X7,X8) = k2_tarski(X7,X8) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_9,plain,(
    ! [X9,X10,X11] : k2_enumset1(X9,X9,X10,X11) = k1_enumset1(X9,X10,X11) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k2_tarski(X4,X5)))
       => ( ( k1_mcart_1(X1) = X2
            | k1_mcart_1(X1) = X3 )
          & ( k2_mcart_1(X1) = X4
            | k2_mcart_1(X1) = X5 ) ) ) ),
    inference(assume_negation,[status(cth)],[t19_mcart_1])).

cnf(c_0_11,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | ~ r2_hidden(X1,X2)
    | X2 != k2_enumset1(X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0)))
    & ( k2_mcart_1(esk2_0) != esk5_0
      | k1_mcart_1(esk2_0) != esk3_0 )
    & ( k2_mcart_1(esk2_0) != esk6_0
      | k1_mcart_1(esk2_0) != esk3_0 )
    & ( k2_mcart_1(esk2_0) != esk5_0
      | k1_mcart_1(esk2_0) != esk4_0 )
    & ( k2_mcart_1(esk2_0) != esk6_0
      | k1_mcart_1(esk2_0) != esk4_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).

cnf(c_0_16,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,k2_enumset1(X5,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k2_zfmisc_1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_13]),c_0_13]),c_0_14]),c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X29,X30] :
      ( k1_mcart_1(k4_tarski(X29,X30)) = X29
      & k2_mcart_1(k4_tarski(X29,X30)) = X30 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_20,plain,
    ( X1 = k4_tarski(X2,X3)
    | X1 = k4_tarski(X2,X4)
    | X1 = k4_tarski(X5,X3)
    | X1 = k4_tarski(X5,X4)
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_enumset1(X5,X5,X5,X2),k2_enumset1(X4,X4,X4,X3))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_13]),c_0_13]),c_0_14]),c_0_14])).

cnf(c_0_22,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( k4_tarski(esk3_0,esk5_0) = esk2_0
    | k4_tarski(esk3_0,esk6_0) = esk2_0
    | k4_tarski(esk4_0,esk5_0) = esk2_0
    | k4_tarski(esk4_0,esk6_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( k2_mcart_1(esk2_0) != esk6_0
    | k1_mcart_1(esk2_0) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( k4_tarski(esk4_0,esk5_0) = esk2_0
    | k4_tarski(esk3_0,esk6_0) = esk2_0
    | k4_tarski(esk3_0,esk5_0) = esk2_0
    | k2_mcart_1(esk2_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( k4_tarski(esk4_0,esk5_0) = esk2_0
    | k4_tarski(esk3_0,esk6_0) = esk2_0
    | k4_tarski(esk3_0,esk5_0) = esk2_0
    | k1_mcart_1(esk2_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( k4_tarski(esk3_0,esk5_0) = esk2_0
    | k4_tarski(esk3_0,esk6_0) = esk2_0
    | k4_tarski(esk4_0,esk5_0) = esk2_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_29,negated_conjecture,
    ( k2_mcart_1(esk2_0) != esk5_0
    | k1_mcart_1(esk2_0) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( k4_tarski(esk3_0,esk6_0) = esk2_0
    | k4_tarski(esk3_0,esk5_0) = esk2_0
    | k2_mcart_1(esk2_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( k4_tarski(esk3_0,esk6_0) = esk2_0
    | k4_tarski(esk3_0,esk5_0) = esk2_0
    | k1_mcart_1(esk2_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( k4_tarski(esk3_0,esk5_0) = esk2_0
    | k4_tarski(esk3_0,esk6_0) = esk2_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_33,negated_conjecture,
    ( k2_mcart_1(esk2_0) != esk6_0
    | k1_mcart_1(esk2_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( k4_tarski(esk3_0,esk5_0) = esk2_0
    | k2_mcart_1(esk2_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( k4_tarski(esk3_0,esk5_0) = esk2_0
    | k1_mcart_1(esk2_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( k4_tarski(esk3_0,esk5_0) = esk2_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_37,negated_conjecture,
    ( k2_mcart_1(esk2_0) != esk5_0
    | k1_mcart_1(esk2_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_38,negated_conjecture,
    ( k1_mcart_1(esk2_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( k2_mcart_1(esk2_0) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38])])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_36]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:59:49 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  # Version: 2.5pre002
% 0.21/0.35  # No SInE strategy applied
% 0.21/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.38  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.21/0.38  # and selection function SelectNegativeLiterals.
% 0.21/0.38  #
% 0.21/0.38  # Preprocessing time       : 0.026 s
% 0.21/0.38  # Presaturation interreduction done
% 0.21/0.38  
% 0.21/0.38  # Proof found!
% 0.21/0.38  # SZS status Theorem
% 0.21/0.38  # SZS output start CNFRefutation
% 0.21/0.38  fof(d2_enumset1, axiom, ![X1, X2, X3, X4, X5]:(X5=k2_enumset1(X1,X2,X3,X4)<=>![X6]:(r2_hidden(X6,X5)<=>~((((X6!=X1&X6!=X2)&X6!=X3)&X6!=X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_enumset1)).
% 0.21/0.38  fof(t146_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_zfmisc_1)).
% 0.21/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.38  fof(t19_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k2_tarski(X4,X5)))=>((k1_mcart_1(X1)=X2|k1_mcart_1(X1)=X3)&(k2_mcart_1(X1)=X4|k2_mcart_1(X1)=X5))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_mcart_1)).
% 0.21/0.38  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.21/0.38  fof(c_0_6, plain, ![X16, X17, X18, X19, X20, X21, X22, X23, X24, X25, X26, X27]:(((~r2_hidden(X21,X20)|(X21=X16|X21=X17|X21=X18|X21=X19)|X20!=k2_enumset1(X16,X17,X18,X19))&((((X22!=X16|r2_hidden(X22,X20)|X20!=k2_enumset1(X16,X17,X18,X19))&(X22!=X17|r2_hidden(X22,X20)|X20!=k2_enumset1(X16,X17,X18,X19)))&(X22!=X18|r2_hidden(X22,X20)|X20!=k2_enumset1(X16,X17,X18,X19)))&(X22!=X19|r2_hidden(X22,X20)|X20!=k2_enumset1(X16,X17,X18,X19))))&(((((esk1_5(X23,X24,X25,X26,X27)!=X23|~r2_hidden(esk1_5(X23,X24,X25,X26,X27),X27)|X27=k2_enumset1(X23,X24,X25,X26))&(esk1_5(X23,X24,X25,X26,X27)!=X24|~r2_hidden(esk1_5(X23,X24,X25,X26,X27),X27)|X27=k2_enumset1(X23,X24,X25,X26)))&(esk1_5(X23,X24,X25,X26,X27)!=X25|~r2_hidden(esk1_5(X23,X24,X25,X26,X27),X27)|X27=k2_enumset1(X23,X24,X25,X26)))&(esk1_5(X23,X24,X25,X26,X27)!=X26|~r2_hidden(esk1_5(X23,X24,X25,X26,X27),X27)|X27=k2_enumset1(X23,X24,X25,X26)))&(r2_hidden(esk1_5(X23,X24,X25,X26,X27),X27)|(esk1_5(X23,X24,X25,X26,X27)=X23|esk1_5(X23,X24,X25,X26,X27)=X24|esk1_5(X23,X24,X25,X26,X27)=X25|esk1_5(X23,X24,X25,X26,X27)=X26)|X27=k2_enumset1(X23,X24,X25,X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_enumset1])])])])])])).
% 0.21/0.38  fof(c_0_7, plain, ![X12, X13, X14, X15]:k2_zfmisc_1(k2_tarski(X12,X13),k2_tarski(X14,X15))=k2_enumset1(k4_tarski(X12,X14),k4_tarski(X12,X15),k4_tarski(X13,X14),k4_tarski(X13,X15)), inference(variable_rename,[status(thm)],[t146_zfmisc_1])).
% 0.21/0.38  fof(c_0_8, plain, ![X7, X8]:k1_enumset1(X7,X7,X8)=k2_tarski(X7,X8), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.38  fof(c_0_9, plain, ![X9, X10, X11]:k2_enumset1(X9,X9,X10,X11)=k1_enumset1(X9,X10,X11), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.38  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k2_tarski(X4,X5)))=>((k1_mcart_1(X1)=X2|k1_mcart_1(X1)=X3)&(k2_mcart_1(X1)=X4|k2_mcart_1(X1)=X5)))), inference(assume_negation,[status(cth)],[t19_mcart_1])).
% 0.21/0.38  cnf(c_0_11, plain, (X1=X3|X1=X4|X1=X5|X1=X6|~r2_hidden(X1,X2)|X2!=k2_enumset1(X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.38  cnf(c_0_12, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.38  cnf(c_0_13, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.38  cnf(c_0_14, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.38  fof(c_0_15, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0)))&(((k2_mcart_1(esk2_0)!=esk5_0|k1_mcart_1(esk2_0)!=esk3_0)&(k2_mcart_1(esk2_0)!=esk6_0|k1_mcart_1(esk2_0)!=esk3_0))&((k2_mcart_1(esk2_0)!=esk5_0|k1_mcart_1(esk2_0)!=esk4_0)&(k2_mcart_1(esk2_0)!=esk6_0|k1_mcart_1(esk2_0)!=esk4_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).
% 0.21/0.38  cnf(c_0_16, plain, (X1=X2|X1=X3|X1=X4|X1=X5|~r2_hidden(X1,k2_enumset1(X5,X4,X3,X2))), inference(er,[status(thm)],[c_0_11])).
% 0.21/0.38  cnf(c_0_17, plain, (k2_zfmisc_1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_13]), c_0_13]), c_0_14]), c_0_14])).
% 0.21/0.38  cnf(c_0_18, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.38  fof(c_0_19, plain, ![X29, X30]:(k1_mcart_1(k4_tarski(X29,X30))=X29&k2_mcart_1(k4_tarski(X29,X30))=X30), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.21/0.38  cnf(c_0_20, plain, (X1=k4_tarski(X2,X3)|X1=k4_tarski(X2,X4)|X1=k4_tarski(X5,X3)|X1=k4_tarski(X5,X4)|~r2_hidden(X1,k2_zfmisc_1(k2_enumset1(X5,X5,X5,X2),k2_enumset1(X4,X4,X4,X3)))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.21/0.38  cnf(c_0_21, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_13]), c_0_13]), c_0_14]), c_0_14])).
% 0.21/0.38  cnf(c_0_22, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.38  cnf(c_0_23, negated_conjecture, (k4_tarski(esk3_0,esk5_0)=esk2_0|k4_tarski(esk3_0,esk6_0)=esk2_0|k4_tarski(esk4_0,esk5_0)=esk2_0|k4_tarski(esk4_0,esk6_0)=esk2_0), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.21/0.38  cnf(c_0_24, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.38  cnf(c_0_25, negated_conjecture, (k2_mcart_1(esk2_0)!=esk6_0|k1_mcart_1(esk2_0)!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.38  cnf(c_0_26, negated_conjecture, (k4_tarski(esk4_0,esk5_0)=esk2_0|k4_tarski(esk3_0,esk6_0)=esk2_0|k4_tarski(esk3_0,esk5_0)=esk2_0|k2_mcart_1(esk2_0)=esk6_0), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.21/0.38  cnf(c_0_27, negated_conjecture, (k4_tarski(esk4_0,esk5_0)=esk2_0|k4_tarski(esk3_0,esk6_0)=esk2_0|k4_tarski(esk3_0,esk5_0)=esk2_0|k1_mcart_1(esk2_0)=esk4_0), inference(spm,[status(thm)],[c_0_24, c_0_23])).
% 0.21/0.38  cnf(c_0_28, negated_conjecture, (k4_tarski(esk3_0,esk5_0)=esk2_0|k4_tarski(esk3_0,esk6_0)=esk2_0|k4_tarski(esk4_0,esk5_0)=esk2_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.21/0.38  cnf(c_0_29, negated_conjecture, (k2_mcart_1(esk2_0)!=esk5_0|k1_mcart_1(esk2_0)!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.38  cnf(c_0_30, negated_conjecture, (k4_tarski(esk3_0,esk6_0)=esk2_0|k4_tarski(esk3_0,esk5_0)=esk2_0|k2_mcart_1(esk2_0)=esk5_0), inference(spm,[status(thm)],[c_0_22, c_0_28])).
% 0.21/0.38  cnf(c_0_31, negated_conjecture, (k4_tarski(esk3_0,esk6_0)=esk2_0|k4_tarski(esk3_0,esk5_0)=esk2_0|k1_mcart_1(esk2_0)=esk4_0), inference(spm,[status(thm)],[c_0_24, c_0_28])).
% 0.21/0.38  cnf(c_0_32, negated_conjecture, (k4_tarski(esk3_0,esk5_0)=esk2_0|k4_tarski(esk3_0,esk6_0)=esk2_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.21/0.38  cnf(c_0_33, negated_conjecture, (k2_mcart_1(esk2_0)!=esk6_0|k1_mcart_1(esk2_0)!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.38  cnf(c_0_34, negated_conjecture, (k4_tarski(esk3_0,esk5_0)=esk2_0|k2_mcart_1(esk2_0)=esk6_0), inference(spm,[status(thm)],[c_0_22, c_0_32])).
% 0.21/0.38  cnf(c_0_35, negated_conjecture, (k4_tarski(esk3_0,esk5_0)=esk2_0|k1_mcart_1(esk2_0)=esk3_0), inference(spm,[status(thm)],[c_0_24, c_0_32])).
% 0.21/0.38  cnf(c_0_36, negated_conjecture, (k4_tarski(esk3_0,esk5_0)=esk2_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.21/0.38  cnf(c_0_37, negated_conjecture, (k2_mcart_1(esk2_0)!=esk5_0|k1_mcart_1(esk2_0)!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.38  cnf(c_0_38, negated_conjecture, (k1_mcart_1(esk2_0)=esk3_0), inference(spm,[status(thm)],[c_0_24, c_0_36])).
% 0.21/0.38  cnf(c_0_39, negated_conjecture, (k2_mcart_1(esk2_0)!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38])])).
% 0.21/0.38  cnf(c_0_40, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_36]), c_0_39]), ['proof']).
% 0.21/0.38  # SZS output end CNFRefutation
% 0.21/0.38  # Proof object total steps             : 41
% 0.21/0.38  # Proof object clause steps            : 28
% 0.21/0.38  # Proof object formula steps           : 13
% 0.21/0.38  # Proof object conjectures             : 22
% 0.21/0.38  # Proof object clause conjectures      : 19
% 0.21/0.38  # Proof object formula conjectures     : 3
% 0.21/0.38  # Proof object initial clauses used    : 11
% 0.21/0.38  # Proof object initial formulas used   : 6
% 0.21/0.38  # Proof object generating inferences   : 13
% 0.21/0.38  # Proof object simplifying inferences  : 15
% 0.21/0.38  # Training examples: 0 positive, 0 negative
% 0.21/0.38  # Parsed axioms                        : 6
% 0.21/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.38  # Initial clauses                      : 20
% 0.21/0.38  # Removed in clause preprocessing      : 2
% 0.21/0.38  # Initial clauses in saturation        : 18
% 0.21/0.38  # Processed clauses                    : 67
% 0.21/0.38  # ...of these trivial                  : 0
% 0.21/0.38  # ...subsumed                          : 1
% 0.21/0.38  # ...remaining for further processing  : 65
% 0.21/0.38  # Other redundant clauses eliminated   : 33
% 0.21/0.38  # Clauses deleted for lack of memory   : 0
% 0.21/0.38  # Backward-subsumed                    : 8
% 0.21/0.38  # Backward-rewritten                   : 9
% 0.21/0.38  # Generated clauses                    : 195
% 0.21/0.38  # ...of the previous two non-trivial   : 168
% 0.21/0.38  # Contextual simplify-reflections      : 3
% 0.21/0.38  # Paramodulations                      : 154
% 0.21/0.38  # Factorizations                       : 12
% 0.21/0.38  # Equation resolutions                 : 33
% 0.21/0.38  # Propositional unsat checks           : 0
% 0.21/0.38  #    Propositional check models        : 0
% 0.21/0.38  #    Propositional check unsatisfiable : 0
% 0.21/0.38  #    Propositional clauses             : 0
% 0.21/0.38  #    Propositional clauses after purity: 0
% 0.21/0.38  #    Propositional unsat core size     : 0
% 0.21/0.38  #    Propositional preprocessing time  : 0.000
% 0.21/0.38  #    Propositional encoding time       : 0.000
% 0.21/0.38  #    Propositional solver time         : 0.000
% 0.21/0.38  #    Success case prop preproc time    : 0.000
% 0.21/0.38  #    Success case prop encoding time   : 0.000
% 0.21/0.38  #    Success case prop solver time     : 0.000
% 0.21/0.38  # Current number of processed clauses  : 25
% 0.21/0.38  #    Positive orientable unit clauses  : 13
% 0.21/0.38  #    Positive unorientable unit clauses: 3
% 0.21/0.38  #    Negative unit clauses             : 2
% 0.21/0.38  #    Non-unit-clauses                  : 7
% 0.21/0.38  # Current number of unprocessed clauses: 137
% 0.21/0.38  # ...number of literals in the above   : 374
% 0.21/0.38  # Current number of archived formulas  : 0
% 0.21/0.38  # Current number of archived clauses   : 37
% 0.21/0.38  # Clause-clause subsumption calls (NU) : 83
% 0.21/0.38  # Rec. Clause-clause subsumption calls : 70
% 0.21/0.38  # Non-unit clause-clause subsumptions  : 11
% 0.21/0.38  # Unit Clause-clause subsumption calls : 2
% 0.21/0.38  # Rewrite failures with RHS unbound    : 0
% 0.21/0.38  # BW rewrite match attempts            : 22
% 0.21/0.38  # BW rewrite match successes           : 4
% 0.21/0.38  # Condensation attempts                : 0
% 0.21/0.38  # Condensation successes               : 0
% 0.21/0.38  # Termbank termtop insertions          : 3640
% 0.21/0.38  
% 0.21/0.38  # -------------------------------------------------
% 0.21/0.38  # User time                : 0.031 s
% 0.21/0.38  # System time              : 0.004 s
% 0.21/0.38  # Total time               : 0.035 s
% 0.21/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
