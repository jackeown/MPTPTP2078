%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:42:18 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 334 expanded)
%              Number of clauses        :   30 ( 137 expanded)
%              Number of leaves         :    8 (  93 expanded)
%              Depth                    :   12
%              Number of atoms          :  144 ( 782 expanded)
%              Number of equality atoms :   78 ( 460 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(X1,k1_tarski(X2)) = X1
      <=> ~ r2_hidden(X2,X1) ) ),
    inference(assume_negation,[status(cth)],[t65_zfmisc_1])).

fof(c_0_9,negated_conjecture,
    ( ( k4_xboole_0(esk4_0,k1_tarski(esk5_0)) != esk4_0
      | r2_hidden(esk5_0,esk4_0) )
    & ( k4_xboole_0(esk4_0,k1_tarski(esk5_0)) = esk4_0
      | ~ r2_hidden(esk5_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_10,plain,(
    ! [X49] : k2_tarski(X49,X49) = k1_tarski(X49) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_11,plain,(
    ! [X50,X51] : k1_enumset1(X50,X50,X51) = k2_tarski(X50,X51) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X28,X29] : k4_xboole_0(X28,X29) = k5_xboole_0(X28,k3_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_13,plain,(
    ! [X52,X53,X54] : k2_enumset1(X52,X52,X53,X54) = k1_enumset1(X52,X53,X54) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_14,plain,(
    ! [X55,X56,X57,X58] : k3_enumset1(X55,X55,X56,X57,X58) = k2_enumset1(X55,X56,X57,X58) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_15,plain,(
    ! [X17,X18,X19,X20,X21,X22,X23,X24] :
      ( ( r2_hidden(X20,X17)
        | ~ r2_hidden(X20,X19)
        | X19 != k4_xboole_0(X17,X18) )
      & ( ~ r2_hidden(X20,X18)
        | ~ r2_hidden(X20,X19)
        | X19 != k4_xboole_0(X17,X18) )
      & ( ~ r2_hidden(X21,X17)
        | r2_hidden(X21,X18)
        | r2_hidden(X21,X19)
        | X19 != k4_xboole_0(X17,X18) )
      & ( ~ r2_hidden(esk2_3(X22,X23,X24),X24)
        | ~ r2_hidden(esk2_3(X22,X23,X24),X22)
        | r2_hidden(esk2_3(X22,X23,X24),X23)
        | X24 = k4_xboole_0(X22,X23) )
      & ( r2_hidden(esk2_3(X22,X23,X24),X22)
        | r2_hidden(esk2_3(X22,X23,X24),X24)
        | X24 = k4_xboole_0(X22,X23) )
      & ( ~ r2_hidden(esk2_3(X22,X23,X24),X23)
        | r2_hidden(esk2_3(X22,X23,X24),X24)
        | X24 = k4_xboole_0(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | k4_xboole_0(esk4_0,k1_tarski(esk5_0)) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,plain,(
    ! [X38,X39,X40,X41,X42,X43,X44,X45,X46,X47] :
      ( ( ~ r2_hidden(X42,X41)
        | X42 = X38
        | X42 = X39
        | X42 = X40
        | X41 != k1_enumset1(X38,X39,X40) )
      & ( X43 != X38
        | r2_hidden(X43,X41)
        | X41 != k1_enumset1(X38,X39,X40) )
      & ( X43 != X39
        | r2_hidden(X43,X41)
        | X41 != k1_enumset1(X38,X39,X40) )
      & ( X43 != X40
        | r2_hidden(X43,X41)
        | X41 != k1_enumset1(X38,X39,X40) )
      & ( esk3_4(X44,X45,X46,X47) != X44
        | ~ r2_hidden(esk3_4(X44,X45,X46,X47),X47)
        | X47 = k1_enumset1(X44,X45,X46) )
      & ( esk3_4(X44,X45,X46,X47) != X45
        | ~ r2_hidden(esk3_4(X44,X45,X46,X47),X47)
        | X47 = k1_enumset1(X44,X45,X46) )
      & ( esk3_4(X44,X45,X46,X47) != X46
        | ~ r2_hidden(esk3_4(X44,X45,X46,X47),X47)
        | X47 = k1_enumset1(X44,X45,X46) )
      & ( r2_hidden(esk3_4(X44,X45,X46,X47),X47)
        | esk3_4(X44,X45,X46,X47) = X44
        | esk3_4(X44,X45,X46,X47) = X45
        | esk3_4(X44,X45,X46,X47) = X46
        | X47 = k1_enumset1(X44,X45,X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_24,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) != esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_26,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_22,c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( k4_xboole_0(esk4_0,k1_tarski(esk5_0)) = esk4_0
    | ~ r2_hidden(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_28,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_24,c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk2_3(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk4_0),esk4_0)
    | r2_hidden(esk5_0,esk4_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26])])).

cnf(c_0_31,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) = esk4_0
    | ~ r2_hidden(esk5_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_32,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_20]),c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) = esk4_0
    | r2_hidden(esk2_3(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk4_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_30]),c_0_31])).

cnf(c_0_34,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk2_3(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk4_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | r2_hidden(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_33])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( esk2_3(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk4_0) = esk5_0
    | r2_hidden(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_36,c_0_19])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_37])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_39])])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_20]),c_0_21])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_43])])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_39])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:35:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.19/0.39  # and selection function SelectNegativeLiterals.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.028 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t65_zfmisc_1, conjecture, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.19/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.39  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.19/0.39  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.19/0.39  fof(c_0_8, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1)))), inference(assume_negation,[status(cth)],[t65_zfmisc_1])).
% 0.19/0.39  fof(c_0_9, negated_conjecture, ((k4_xboole_0(esk4_0,k1_tarski(esk5_0))!=esk4_0|r2_hidden(esk5_0,esk4_0))&(k4_xboole_0(esk4_0,k1_tarski(esk5_0))=esk4_0|~r2_hidden(esk5_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.19/0.39  fof(c_0_10, plain, ![X49]:k2_tarski(X49,X49)=k1_tarski(X49), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.39  fof(c_0_11, plain, ![X50, X51]:k1_enumset1(X50,X50,X51)=k2_tarski(X50,X51), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.39  fof(c_0_12, plain, ![X28, X29]:k4_xboole_0(X28,X29)=k5_xboole_0(X28,k3_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.39  fof(c_0_13, plain, ![X52, X53, X54]:k2_enumset1(X52,X52,X53,X54)=k1_enumset1(X52,X53,X54), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.39  fof(c_0_14, plain, ![X55, X56, X57, X58]:k3_enumset1(X55,X55,X56,X57,X58)=k2_enumset1(X55,X56,X57,X58), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.39  fof(c_0_15, plain, ![X17, X18, X19, X20, X21, X22, X23, X24]:((((r2_hidden(X20,X17)|~r2_hidden(X20,X19)|X19!=k4_xboole_0(X17,X18))&(~r2_hidden(X20,X18)|~r2_hidden(X20,X19)|X19!=k4_xboole_0(X17,X18)))&(~r2_hidden(X21,X17)|r2_hidden(X21,X18)|r2_hidden(X21,X19)|X19!=k4_xboole_0(X17,X18)))&((~r2_hidden(esk2_3(X22,X23,X24),X24)|(~r2_hidden(esk2_3(X22,X23,X24),X22)|r2_hidden(esk2_3(X22,X23,X24),X23))|X24=k4_xboole_0(X22,X23))&((r2_hidden(esk2_3(X22,X23,X24),X22)|r2_hidden(esk2_3(X22,X23,X24),X24)|X24=k4_xboole_0(X22,X23))&(~r2_hidden(esk2_3(X22,X23,X24),X23)|r2_hidden(esk2_3(X22,X23,X24),X24)|X24=k4_xboole_0(X22,X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.19/0.39  cnf(c_0_16, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|k4_xboole_0(esk4_0,k1_tarski(esk5_0))!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_17, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_20, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_21, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.39  cnf(c_0_22, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.39  fof(c_0_23, plain, ![X38, X39, X40, X41, X42, X43, X44, X45, X46, X47]:(((~r2_hidden(X42,X41)|(X42=X38|X42=X39|X42=X40)|X41!=k1_enumset1(X38,X39,X40))&(((X43!=X38|r2_hidden(X43,X41)|X41!=k1_enumset1(X38,X39,X40))&(X43!=X39|r2_hidden(X43,X41)|X41!=k1_enumset1(X38,X39,X40)))&(X43!=X40|r2_hidden(X43,X41)|X41!=k1_enumset1(X38,X39,X40))))&((((esk3_4(X44,X45,X46,X47)!=X44|~r2_hidden(esk3_4(X44,X45,X46,X47),X47)|X47=k1_enumset1(X44,X45,X46))&(esk3_4(X44,X45,X46,X47)!=X45|~r2_hidden(esk3_4(X44,X45,X46,X47),X47)|X47=k1_enumset1(X44,X45,X46)))&(esk3_4(X44,X45,X46,X47)!=X46|~r2_hidden(esk3_4(X44,X45,X46,X47),X47)|X47=k1_enumset1(X44,X45,X46)))&(r2_hidden(esk3_4(X44,X45,X46,X47),X47)|(esk3_4(X44,X45,X46,X47)=X44|esk3_4(X44,X45,X46,X47)=X45|esk3_4(X44,X45,X46,X47)=X46)|X47=k1_enumset1(X44,X45,X46)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.19/0.39  cnf(c_0_24, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.39  cnf(c_0_25, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))!=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21])).
% 0.19/0.39  cnf(c_0_26, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_22, c_0_19])).
% 0.19/0.39  cnf(c_0_27, negated_conjecture, (k4_xboole_0(esk4_0,k1_tarski(esk5_0))=esk4_0|~r2_hidden(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_28, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.39  cnf(c_0_29, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_24, c_0_19])).
% 0.19/0.39  cnf(c_0_30, negated_conjecture, (r2_hidden(esk2_3(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk4_0),esk4_0)|r2_hidden(esk5_0,esk4_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26])])).
% 0.19/0.39  cnf(c_0_31, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))=esk4_0|~r2_hidden(esk5_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21])).
% 0.19/0.39  cnf(c_0_32, plain, (X1=X5|X1=X4|X1=X3|X2!=k3_enumset1(X3,X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_20]), c_0_21])).
% 0.19/0.39  cnf(c_0_33, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))=esk4_0|r2_hidden(esk2_3(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk4_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_30]), c_0_31])).
% 0.19/0.39  cnf(c_0_34, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_32])).
% 0.19/0.39  cnf(c_0_35, negated_conjecture, (r2_hidden(esk2_3(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk4_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|r2_hidden(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_25, c_0_33])).
% 0.19/0.39  cnf(c_0_36, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.39  cnf(c_0_37, negated_conjecture, (esk2_3(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk4_0)=esk5_0|r2_hidden(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.39  cnf(c_0_38, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_36, c_0_19])).
% 0.19/0.39  cnf(c_0_39, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_30, c_0_37])).
% 0.19/0.39  cnf(c_0_40, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.39  cnf(c_0_41, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_38])).
% 0.19/0.39  cnf(c_0_42, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_39])])).
% 0.19/0.39  cnf(c_0_43, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_20]), c_0_21])).
% 0.19/0.39  cnf(c_0_44, negated_conjecture, (~r2_hidden(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.39  cnf(c_0_45, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_43])])).
% 0.19/0.39  cnf(c_0_46, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_39])]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 47
% 0.19/0.39  # Proof object clause steps            : 30
% 0.19/0.39  # Proof object formula steps           : 17
% 0.19/0.39  # Proof object conjectures             : 15
% 0.19/0.39  # Proof object clause conjectures      : 12
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 12
% 0.19/0.39  # Proof object initial formulas used   : 8
% 0.19/0.39  # Proof object generating inferences   : 7
% 0.19/0.39  # Proof object simplifying inferences  : 28
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 17
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 38
% 0.19/0.39  # Removed in clause preprocessing      : 5
% 0.19/0.39  # Initial clauses in saturation        : 33
% 0.19/0.39  # Processed clauses                    : 306
% 0.19/0.39  # ...of these trivial                  : 36
% 0.19/0.39  # ...subsumed                          : 131
% 0.19/0.39  # ...remaining for further processing  : 139
% 0.19/0.39  # Other redundant clauses eliminated   : 73
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 1
% 0.19/0.39  # Backward-rewritten                   : 19
% 0.19/0.39  # Generated clauses                    : 1733
% 0.19/0.39  # ...of the previous two non-trivial   : 1447
% 0.19/0.39  # Contextual simplify-reflections      : 3
% 0.19/0.39  # Paramodulations                      : 1657
% 0.19/0.39  # Factorizations                       : 6
% 0.19/0.39  # Equation resolutions                 : 73
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 74
% 0.19/0.39  #    Positive orientable unit clauses  : 20
% 0.19/0.39  #    Positive unorientable unit clauses: 1
% 0.19/0.39  #    Negative unit clauses             : 1
% 0.19/0.39  #    Non-unit-clauses                  : 52
% 0.19/0.39  # Current number of unprocessed clauses: 1171
% 0.19/0.39  # ...number of literals in the above   : 3857
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 57
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 1374
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 1055
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 72
% 0.19/0.39  # Unit Clause-clause subsumption calls : 63
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 40
% 0.19/0.39  # BW rewrite match successes           : 18
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 23338
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.055 s
% 0.19/0.40  # System time              : 0.002 s
% 0.19/0.40  # Total time               : 0.057 s
% 0.19/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
