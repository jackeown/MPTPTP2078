%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:11 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 179 expanded)
%              Number of clauses        :   24 (  72 expanded)
%              Number of leaves         :    8 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :  117 ( 321 expanded)
%              Number of equality atoms :   75 ( 235 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t17_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k1_tarski(X4)))
     => ( ( k1_mcart_1(X1) = X2
          | k1_mcart_1(X1) = X3 )
        & k2_mcart_1(X1) = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_mcart_1)).

fof(t23_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X1 != X2
     => k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X2)) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_zfmisc_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(c_0_8,plain,(
    ! [X25,X26,X27] :
      ( ( r2_hidden(X25,X26)
        | ~ r2_hidden(X25,k4_xboole_0(X26,k1_tarski(X27))) )
      & ( X25 != X27
        | ~ r2_hidden(X25,k4_xboole_0(X26,k1_tarski(X27))) )
      & ( ~ r2_hidden(X25,X26)
        | X25 = X27
        | r2_hidden(X25,k4_xboole_0(X26,k1_tarski(X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_9,plain,(
    ! [X17] : k2_tarski(X17,X17) = k1_tarski(X17) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_10,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_11,plain,(
    ! [X20,X21,X22] : k2_enumset1(X20,X20,X21,X22) = k1_enumset1(X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k1_tarski(X4)))
       => ( ( k1_mcart_1(X1) = X2
            | k1_mcart_1(X1) = X3 )
          & k2_mcart_1(X1) = X4 ) ) ),
    inference(assume_negation,[status(cth)],[t17_mcart_1])).

cnf(c_0_13,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X23,X24] :
      ( X23 = X24
      | k4_xboole_0(k2_tarski(X23,X24),k1_tarski(X24)) = k1_tarski(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_zfmisc_1])])).

fof(c_0_18,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0)))
    & ( k1_mcart_1(esk2_0) != esk3_0
      | k2_mcart_1(esk2_0) != esk5_0 )
    & ( k1_mcart_1(esk2_0) != esk4_0
      | k2_mcart_1(esk2_0) != esk5_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).

cnf(c_0_19,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k2_enumset1(X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])).

cnf(c_0_20,plain,
    ( X1 = X2
    | k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X2)) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X28,X29,X30] :
      ( ( r2_hidden(k1_mcart_1(X28),X29)
        | ~ r2_hidden(X28,k2_zfmisc_1(X29,X30)) )
      & ( r2_hidden(k2_mcart_1(X28),X30)
        | ~ r2_hidden(X28,k2_zfmisc_1(X29,X30)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X10,X9)
        | X10 = X6
        | X10 = X7
        | X10 = X8
        | X9 != k1_enumset1(X6,X7,X8) )
      & ( X11 != X6
        | r2_hidden(X11,X9)
        | X9 != k1_enumset1(X6,X7,X8) )
      & ( X11 != X7
        | r2_hidden(X11,X9)
        | X9 != k1_enumset1(X6,X7,X8) )
      & ( X11 != X8
        | r2_hidden(X11,X9)
        | X9 != k1_enumset1(X6,X7,X8) )
      & ( esk1_4(X12,X13,X14,X15) != X12
        | ~ r2_hidden(esk1_4(X12,X13,X14,X15),X15)
        | X15 = k1_enumset1(X12,X13,X14) )
      & ( esk1_4(X12,X13,X14,X15) != X13
        | ~ r2_hidden(esk1_4(X12,X13,X14,X15),X15)
        | X15 = k1_enumset1(X12,X13,X14) )
      & ( esk1_4(X12,X13,X14,X15) != X14
        | ~ r2_hidden(esk1_4(X12,X13,X14,X15),X15)
        | X15 = k1_enumset1(X12,X13,X14) )
      & ( r2_hidden(esk1_4(X12,X13,X14,X15),X15)
        | esk1_4(X12,X13,X14,X15) = X12
        | esk1_4(X12,X13,X14,X15) = X13
        | esk1_4(X12,X13,X14,X15) = X14
        | X15 = k1_enumset1(X12,X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( X1 = X2
    | k4_xboole_0(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_14]),c_0_14]),c_0_15]),c_0_15]),c_0_15]),c_0_16]),c_0_16]),c_0_16])).

cnf(c_0_26,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_14]),c_0_15]),c_0_15]),c_0_16]),c_0_16])).

cnf(c_0_28,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( X1 = X2
    | ~ r2_hidden(X2,k2_enumset1(X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k2_enumset1(X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_28,c_0_16])).

cnf(c_0_32,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( k1_mcart_1(esk2_0) != esk3_0
    | k2_mcart_1(esk2_0) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,negated_conjecture,
    ( esk5_0 = k2_mcart_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( k1_mcart_1(esk2_0) != esk4_0
    | k2_mcart_1(esk2_0) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_36,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X3,X4)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( esk3_0 != k1_mcart_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34])])).

cnf(c_0_39,negated_conjecture,
    ( esk4_0 != k1_mcart_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_34])])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:04:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.13/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.38  fof(t17_mcart_1, conjecture, ![X1, X2, X3, X4]:(r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k1_tarski(X4)))=>((k1_mcart_1(X1)=X2|k1_mcart_1(X1)=X3)&k2_mcart_1(X1)=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_mcart_1)).
% 0.13/0.38  fof(t23_zfmisc_1, axiom, ![X1, X2]:(X1!=X2=>k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X2))=k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_zfmisc_1)).
% 0.13/0.38  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.13/0.38  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.13/0.38  fof(c_0_8, plain, ![X25, X26, X27]:(((r2_hidden(X25,X26)|~r2_hidden(X25,k4_xboole_0(X26,k1_tarski(X27))))&(X25!=X27|~r2_hidden(X25,k4_xboole_0(X26,k1_tarski(X27)))))&(~r2_hidden(X25,X26)|X25=X27|r2_hidden(X25,k4_xboole_0(X26,k1_tarski(X27))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.13/0.38  fof(c_0_9, plain, ![X17]:k2_tarski(X17,X17)=k1_tarski(X17), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.38  fof(c_0_10, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  fof(c_0_11, plain, ![X20, X21, X22]:k2_enumset1(X20,X20,X21,X22)=k1_enumset1(X20,X21,X22), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.38  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4]:(r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k1_tarski(X4)))=>((k1_mcart_1(X1)=X2|k1_mcart_1(X1)=X3)&k2_mcart_1(X1)=X4))), inference(assume_negation,[status(cth)],[t17_mcart_1])).
% 0.13/0.38  cnf(c_0_13, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_14, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_16, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  fof(c_0_17, plain, ![X23, X24]:(X23=X24|k4_xboole_0(k2_tarski(X23,X24),k1_tarski(X24))=k1_tarski(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_zfmisc_1])])).
% 0.13/0.38  fof(c_0_18, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0)))&((k1_mcart_1(esk2_0)!=esk3_0|k2_mcart_1(esk2_0)!=esk5_0)&(k1_mcart_1(esk2_0)!=esk4_0|k2_mcart_1(esk2_0)!=esk5_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).
% 0.13/0.38  cnf(c_0_19, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k2_enumset1(X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16])).
% 0.13/0.38  cnf(c_0_20, plain, (X1=X2|k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X2))=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  fof(c_0_21, plain, ![X28, X29, X30]:((r2_hidden(k1_mcart_1(X28),X29)|~r2_hidden(X28,k2_zfmisc_1(X29,X30)))&(r2_hidden(k2_mcart_1(X28),X30)|~r2_hidden(X28,k2_zfmisc_1(X29,X30)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  fof(c_0_23, plain, ![X6, X7, X8, X9, X10, X11, X12, X13, X14, X15]:(((~r2_hidden(X10,X9)|(X10=X6|X10=X7|X10=X8)|X9!=k1_enumset1(X6,X7,X8))&(((X11!=X6|r2_hidden(X11,X9)|X9!=k1_enumset1(X6,X7,X8))&(X11!=X7|r2_hidden(X11,X9)|X9!=k1_enumset1(X6,X7,X8)))&(X11!=X8|r2_hidden(X11,X9)|X9!=k1_enumset1(X6,X7,X8))))&((((esk1_4(X12,X13,X14,X15)!=X12|~r2_hidden(esk1_4(X12,X13,X14,X15),X15)|X15=k1_enumset1(X12,X13,X14))&(esk1_4(X12,X13,X14,X15)!=X13|~r2_hidden(esk1_4(X12,X13,X14,X15),X15)|X15=k1_enumset1(X12,X13,X14)))&(esk1_4(X12,X13,X14,X15)!=X14|~r2_hidden(esk1_4(X12,X13,X14,X15),X15)|X15=k1_enumset1(X12,X13,X14)))&(r2_hidden(esk1_4(X12,X13,X14,X15),X15)|(esk1_4(X12,X13,X14,X15)=X12|esk1_4(X12,X13,X14,X15)=X13|esk1_4(X12,X13,X14,X15)=X14)|X15=k1_enumset1(X12,X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.13/0.38  cnf(c_0_24, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)))), inference(er,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_25, plain, (X1=X2|k4_xboole_0(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X2,X2,X2,X2))=k2_enumset1(X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_14]), c_0_14]), c_0_15]), c_0_15]), c_0_15]), c_0_16]), c_0_16]), c_0_16])).
% 0.13/0.38  cnf(c_0_26, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_14]), c_0_15]), c_0_15]), c_0_16]), c_0_16])).
% 0.13/0.38  cnf(c_0_28, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_29, plain, (X1=X2|~r2_hidden(X2,k2_enumset1(X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.38  cnf(c_0_31, plain, (X1=X5|X1=X4|X1=X3|X2!=k2_enumset1(X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_28, c_0_16])).
% 0.13/0.38  cnf(c_0_32, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (k1_mcart_1(esk2_0)!=esk3_0|k2_mcart_1(esk2_0)!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (esk5_0=k2_mcart_1(esk2_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (k1_mcart_1(esk2_0)!=esk4_0|k2_mcart_1(esk2_0)!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_36, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k2_enumset1(X2,X2,X3,X4))), inference(er,[status(thm)],[c_0_31])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (r2_hidden(k1_mcart_1(esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_32, c_0_27])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (esk3_0!=k1_mcart_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34])])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (esk4_0!=k1_mcart_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_34])])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 41
% 0.13/0.38  # Proof object clause steps            : 24
% 0.13/0.38  # Proof object formula steps           : 17
% 0.13/0.38  # Proof object conjectures             : 13
% 0.13/0.38  # Proof object clause conjectures      : 10
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 11
% 0.13/0.38  # Proof object initial formulas used   : 8
% 0.13/0.38  # Proof object generating inferences   : 6
% 0.13/0.38  # Proof object simplifying inferences  : 24
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 8
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 20
% 0.13/0.38  # Removed in clause preprocessing      : 3
% 0.13/0.38  # Initial clauses in saturation        : 17
% 0.13/0.38  # Processed clauses                    : 48
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 47
% 0.13/0.38  # Other redundant clauses eliminated   : 4
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 4
% 0.13/0.38  # Generated clauses                    : 36
% 0.13/0.38  # ...of the previous two non-trivial   : 38
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 28
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 8
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
% 0.13/0.38  # Current number of processed clauses  : 22
% 0.13/0.38  #    Positive orientable unit clauses  : 5
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 3
% 0.13/0.38  #    Non-unit-clauses                  : 14
% 0.13/0.38  # Current number of unprocessed clauses: 23
% 0.13/0.38  # ...number of literals in the above   : 69
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 24
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 57
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 54
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.38  # Unit Clause-clause subsumption calls : 4
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 10
% 0.13/0.38  # BW rewrite match successes           : 1
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 1535
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.029 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.033 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
