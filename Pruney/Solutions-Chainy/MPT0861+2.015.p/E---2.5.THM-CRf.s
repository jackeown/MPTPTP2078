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
% DateTime   : Thu Dec  3 10:59:12 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 175 expanded)
%              Number of clauses        :   23 (  70 expanded)
%              Number of leaves         :    8 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :  110 ( 345 expanded)
%              Number of equality atoms :   55 ( 236 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k1_tarski(X4)))
     => ( ( k1_mcart_1(X1) = X2
          | k1_mcart_1(X1) = X3 )
        & k2_mcart_1(X1) = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_mcart_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t16_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,k2_tarski(X3,X4)))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & ( k2_mcart_1(X1) = X3
          | k2_mcart_1(X1) = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k1_tarski(X4)))
       => ( ( k1_mcart_1(X1) = X2
            | k1_mcart_1(X1) = X3 )
          & k2_mcart_1(X1) = X4 ) ) ),
    inference(assume_negation,[status(cth)],[t17_mcart_1])).

fof(c_0_9,negated_conjecture,
    ( r2_hidden(esk7_0,k2_zfmisc_1(k2_tarski(esk8_0,esk9_0),k1_tarski(esk10_0)))
    & ( k1_mcart_1(esk7_0) != esk8_0
      | k2_mcart_1(esk7_0) != esk10_0 )
    & ( k1_mcart_1(esk7_0) != esk9_0
      | k2_mcart_1(esk7_0) != esk10_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).

fof(c_0_10,plain,(
    ! [X16] : k2_tarski(X16,X16) = k1_tarski(X16) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_11,plain,(
    ! [X17,X18] : k1_enumset1(X17,X17,X18) = k2_tarski(X17,X18) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X19,X20,X21] : k2_enumset1(X19,X19,X20,X21) = k1_enumset1(X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_13,plain,(
    ! [X44,X45,X46,X47] :
      ( ( r2_hidden(k1_mcart_1(X44),X45)
        | ~ r2_hidden(X44,k2_zfmisc_1(X45,k2_tarski(X46,X47))) )
      & ( k2_mcart_1(X44) = X46
        | k2_mcart_1(X44) = X47
        | ~ r2_hidden(X44,k2_zfmisc_1(X45,k2_tarski(X46,X47))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_mcart_1])])])).

fof(c_0_14,plain,(
    ! [X41,X42,X43] :
      ( ( r2_hidden(k1_mcart_1(X41),X42)
        | ~ r2_hidden(X41,k2_zfmisc_1(X42,X43)) )
      & ( r2_hidden(k2_mcart_1(X41),X43)
        | ~ r2_hidden(X41,k2_zfmisc_1(X42,X43)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk7_0,k2_zfmisc_1(k2_tarski(esk8_0,esk9_0),k1_tarski(esk10_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k2_mcart_1(X1) = X2
    | k2_mcart_1(X1) = X3
    | ~ r2_hidden(X1,k2_zfmisc_1(X4,k2_tarski(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X22,X23,X24,X25,X28,X29,X30,X31,X32,X33,X35,X36] :
      ( ( r2_hidden(esk2_4(X22,X23,X24,X25),X22)
        | ~ r2_hidden(X25,X24)
        | X24 != k2_zfmisc_1(X22,X23) )
      & ( r2_hidden(esk3_4(X22,X23,X24,X25),X23)
        | ~ r2_hidden(X25,X24)
        | X24 != k2_zfmisc_1(X22,X23) )
      & ( X25 = k4_tarski(esk2_4(X22,X23,X24,X25),esk3_4(X22,X23,X24,X25))
        | ~ r2_hidden(X25,X24)
        | X24 != k2_zfmisc_1(X22,X23) )
      & ( ~ r2_hidden(X29,X22)
        | ~ r2_hidden(X30,X23)
        | X28 != k4_tarski(X29,X30)
        | r2_hidden(X28,X24)
        | X24 != k2_zfmisc_1(X22,X23) )
      & ( ~ r2_hidden(esk4_3(X31,X32,X33),X33)
        | ~ r2_hidden(X35,X31)
        | ~ r2_hidden(X36,X32)
        | esk4_3(X31,X32,X33) != k4_tarski(X35,X36)
        | X33 = k2_zfmisc_1(X31,X32) )
      & ( r2_hidden(esk5_3(X31,X32,X33),X31)
        | r2_hidden(esk4_3(X31,X32,X33),X33)
        | X33 = k2_zfmisc_1(X31,X32) )
      & ( r2_hidden(esk6_3(X31,X32,X33),X32)
        | r2_hidden(esk4_3(X31,X32,X33),X33)
        | X33 = k2_zfmisc_1(X31,X32) )
      & ( esk4_3(X31,X32,X33) = k4_tarski(esk5_3(X31,X32,X33),esk6_3(X31,X32,X33))
        | r2_hidden(esk4_3(X31,X32,X33),X33)
        | X33 = k2_zfmisc_1(X31,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_21,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk7_0,k2_zfmisc_1(k2_enumset1(esk8_0,esk8_0,esk8_0,esk9_0),k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_17]),c_0_18]),c_0_18])).

cnf(c_0_23,plain,
    ( k2_mcart_1(X1) = X3
    | k2_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(X4,k2_enumset1(X2,X2,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_17]),c_0_18])).

cnf(c_0_24,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk7_0),k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( k2_mcart_1(esk7_0) = esk10_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_24])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk10_0,k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k4_tarski(esk10_0,X1),k2_zfmisc_1(k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0),X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_22])).

fof(c_0_32,plain,(
    ! [X48,X49] :
      ( k1_mcart_1(k4_tarski(X48,X49)) = X48
      & k2_mcart_1(k4_tarski(X48,X49)) = X49 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_33,negated_conjecture,
    ( k1_mcart_1(esk7_0) != esk9_0
    | k2_mcart_1(esk7_0) != esk10_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,negated_conjecture,
    ( k1_mcart_1(esk7_0) != esk8_0
    | k2_mcart_1(esk7_0) != esk10_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k4_tarski(esk10_0,k1_mcart_1(esk7_0)),k2_zfmisc_1(k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( k1_mcart_1(esk7_0) != esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_26])])).

cnf(c_0_38,negated_conjecture,
    ( k1_mcart_1(esk7_0) != esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_26])])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_38]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:13:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.13/0.38  # and selection function SelectNegativeLiterals.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t17_mcart_1, conjecture, ![X1, X2, X3, X4]:(r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k1_tarski(X4)))=>((k1_mcart_1(X1)=X2|k1_mcart_1(X1)=X3)&k2_mcart_1(X1)=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_mcart_1)).
% 0.13/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.38  fof(t16_mcart_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(X1,k2_zfmisc_1(X2,k2_tarski(X3,X4)))=>(r2_hidden(k1_mcart_1(X1),X2)&(k2_mcart_1(X1)=X3|k2_mcart_1(X1)=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_mcart_1)).
% 0.13/0.38  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.13/0.38  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.13/0.38  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.13/0.38  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3, X4]:(r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k1_tarski(X4)))=>((k1_mcart_1(X1)=X2|k1_mcart_1(X1)=X3)&k2_mcart_1(X1)=X4))), inference(assume_negation,[status(cth)],[t17_mcart_1])).
% 0.13/0.38  fof(c_0_9, negated_conjecture, (r2_hidden(esk7_0,k2_zfmisc_1(k2_tarski(esk8_0,esk9_0),k1_tarski(esk10_0)))&((k1_mcart_1(esk7_0)!=esk8_0|k2_mcart_1(esk7_0)!=esk10_0)&(k1_mcart_1(esk7_0)!=esk9_0|k2_mcart_1(esk7_0)!=esk10_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).
% 0.13/0.38  fof(c_0_10, plain, ![X16]:k2_tarski(X16,X16)=k1_tarski(X16), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.38  fof(c_0_11, plain, ![X17, X18]:k1_enumset1(X17,X17,X18)=k2_tarski(X17,X18), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  fof(c_0_12, plain, ![X19, X20, X21]:k2_enumset1(X19,X19,X20,X21)=k1_enumset1(X19,X20,X21), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.38  fof(c_0_13, plain, ![X44, X45, X46, X47]:((r2_hidden(k1_mcart_1(X44),X45)|~r2_hidden(X44,k2_zfmisc_1(X45,k2_tarski(X46,X47))))&(k2_mcart_1(X44)=X46|k2_mcart_1(X44)=X47|~r2_hidden(X44,k2_zfmisc_1(X45,k2_tarski(X46,X47))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_mcart_1])])])).
% 0.13/0.38  fof(c_0_14, plain, ![X41, X42, X43]:((r2_hidden(k1_mcart_1(X41),X42)|~r2_hidden(X41,k2_zfmisc_1(X42,X43)))&(r2_hidden(k2_mcart_1(X41),X43)|~r2_hidden(X41,k2_zfmisc_1(X42,X43)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.13/0.38  cnf(c_0_15, negated_conjecture, (r2_hidden(esk7_0,k2_zfmisc_1(k2_tarski(esk8_0,esk9_0),k1_tarski(esk10_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_16, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_18, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_19, plain, (k2_mcart_1(X1)=X2|k2_mcart_1(X1)=X3|~r2_hidden(X1,k2_zfmisc_1(X4,k2_tarski(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  fof(c_0_20, plain, ![X22, X23, X24, X25, X28, X29, X30, X31, X32, X33, X35, X36]:(((((r2_hidden(esk2_4(X22,X23,X24,X25),X22)|~r2_hidden(X25,X24)|X24!=k2_zfmisc_1(X22,X23))&(r2_hidden(esk3_4(X22,X23,X24,X25),X23)|~r2_hidden(X25,X24)|X24!=k2_zfmisc_1(X22,X23)))&(X25=k4_tarski(esk2_4(X22,X23,X24,X25),esk3_4(X22,X23,X24,X25))|~r2_hidden(X25,X24)|X24!=k2_zfmisc_1(X22,X23)))&(~r2_hidden(X29,X22)|~r2_hidden(X30,X23)|X28!=k4_tarski(X29,X30)|r2_hidden(X28,X24)|X24!=k2_zfmisc_1(X22,X23)))&((~r2_hidden(esk4_3(X31,X32,X33),X33)|(~r2_hidden(X35,X31)|~r2_hidden(X36,X32)|esk4_3(X31,X32,X33)!=k4_tarski(X35,X36))|X33=k2_zfmisc_1(X31,X32))&(((r2_hidden(esk5_3(X31,X32,X33),X31)|r2_hidden(esk4_3(X31,X32,X33),X33)|X33=k2_zfmisc_1(X31,X32))&(r2_hidden(esk6_3(X31,X32,X33),X32)|r2_hidden(esk4_3(X31,X32,X33),X33)|X33=k2_zfmisc_1(X31,X32)))&(esk4_3(X31,X32,X33)=k4_tarski(esk5_3(X31,X32,X33),esk6_3(X31,X32,X33))|r2_hidden(esk4_3(X31,X32,X33),X33)|X33=k2_zfmisc_1(X31,X32))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.13/0.38  cnf(c_0_21, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (r2_hidden(esk7_0,k2_zfmisc_1(k2_enumset1(esk8_0,esk8_0,esk8_0,esk9_0),k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_17]), c_0_18]), c_0_18])).
% 0.13/0.38  cnf(c_0_23, plain, (k2_mcart_1(X1)=X3|k2_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(X4,k2_enumset1(X2,X2,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_17]), c_0_18])).
% 0.13/0.38  cnf(c_0_24, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k4_tarski(X1,X3)|X6!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (r2_hidden(k2_mcart_1(esk7_0),k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (k2_mcart_1(esk7_0)=esk10_0), inference(spm,[status(thm)],[c_0_23, c_0_22])).
% 0.13/0.38  cnf(c_0_27, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_24])])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (r2_hidden(esk10_0,k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.38  cnf(c_0_29, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (r2_hidden(k4_tarski(esk10_0,X1),k2_zfmisc_1(k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0),X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (r2_hidden(k1_mcart_1(esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_29, c_0_22])).
% 0.13/0.38  fof(c_0_32, plain, ![X48, X49]:(k1_mcart_1(k4_tarski(X48,X49))=X48&k2_mcart_1(k4_tarski(X48,X49))=X49), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (k1_mcart_1(esk7_0)!=esk9_0|k2_mcart_1(esk7_0)!=esk10_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (k1_mcart_1(esk7_0)!=esk8_0|k2_mcart_1(esk7_0)!=esk10_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (r2_hidden(k4_tarski(esk10_0,k1_mcart_1(esk7_0)),k2_zfmisc_1(k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk9_0)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.38  cnf(c_0_36, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (k1_mcart_1(esk7_0)!=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_26])])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (k1_mcart_1(esk7_0)!=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_26])])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_38]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 40
% 0.13/0.38  # Proof object clause steps            : 23
% 0.13/0.38  # Proof object formula steps           : 17
% 0.13/0.38  # Proof object conjectures             : 16
% 0.13/0.38  # Proof object clause conjectures      : 13
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 11
% 0.13/0.38  # Proof object initial formulas used   : 8
% 0.13/0.38  # Proof object generating inferences   : 6
% 0.13/0.38  # Proof object simplifying inferences  : 18
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 10
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 28
% 0.13/0.38  # Removed in clause preprocessing      : 3
% 0.13/0.38  # Initial clauses in saturation        : 25
% 0.13/0.38  # Processed clauses                    : 70
% 0.13/0.38  # ...of these trivial                  : 1
% 0.13/0.38  # ...subsumed                          : 2
% 0.13/0.38  # ...remaining for further processing  : 67
% 0.13/0.38  # Other redundant clauses eliminated   : 9
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 4
% 0.13/0.38  # Generated clauses                    : 142
% 0.13/0.38  # ...of the previous two non-trivial   : 120
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 134
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 9
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
% 0.13/0.38  # Current number of processed clauses  : 32
% 0.13/0.38  #    Positive orientable unit clauses  : 8
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 22
% 0.13/0.38  # Current number of unprocessed clauses: 91
% 0.13/0.38  # ...number of literals in the above   : 284
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 31
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 79
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 53
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.13/0.38  # Unit Clause-clause subsumption calls : 0
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 1
% 0.13/0.38  # BW rewrite match successes           : 1
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 4283
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.032 s
% 0.13/0.38  # System time              : 0.003 s
% 0.13/0.38  # Total time               : 0.035 s
% 0.13/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
