%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:38:45 EST 2020

% Result     : Theorem 0.10s
% Output     : CNFRefutation 0.10s
% Verified   : 
% Statistics : Number of formulae       :   44 (  81 expanded)
%              Number of clauses        :   25 (  34 expanded)
%              Number of leaves         :    9 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  105 ( 180 expanded)
%              Number of equality atoms :   50 ( 106 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))
        & X1 != X2
        & X1 != X3 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))
          & X1 != X2
          & X1 != X3 ) ),
    inference(assume_negation,[status(cth)],[t25_zfmisc_1])).

fof(c_0_10,plain,(
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
      & ( esk3_3(X22,X23,X24) != X22
        | ~ r2_hidden(esk3_3(X22,X23,X24),X24)
        | X24 = k2_tarski(X22,X23) )
      & ( esk3_3(X22,X23,X24) != X23
        | ~ r2_hidden(esk3_3(X22,X23,X24),X24)
        | X24 = k2_tarski(X22,X23) )
      & ( r2_hidden(esk3_3(X22,X23,X24),X24)
        | esk3_3(X22,X23,X24) = X22
        | esk3_3(X22,X23,X24) = X23
        | X24 = k2_tarski(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_11,plain,(
    ! [X27,X28] : k1_enumset1(X27,X27,X28) = k2_tarski(X27,X28) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X29,X30,X31] : k2_enumset1(X29,X29,X30,X31) = k1_enumset1(X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_13,negated_conjecture,
    ( r1_tarski(k1_tarski(esk4_0),k2_tarski(esk5_0,esk6_0))
    & esk4_0 != esk5_0
    & esk4_0 != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_14,plain,(
    ! [X26] : k2_tarski(X26,X26) = k1_tarski(X26) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X9,X10,X12,X13,X14] :
      ( ( r1_xboole_0(X9,X10)
        | r2_hidden(esk2_2(X9,X10),k3_xboole_0(X9,X10)) )
      & ( ~ r2_hidden(X14,k3_xboole_0(X12,X13))
        | ~ r1_xboole_0(X12,X13) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_19,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_20,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k3_xboole_0(X15,X16) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(k1_tarski(esk4_0),k2_tarski(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_16]),c_0_16]),c_0_17]),c_0_17])).

cnf(c_0_28,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_23])])).

fof(c_0_30,plain,(
    ! [X32,X33] :
      ( r2_hidden(X32,X33)
      | r1_xboole_0(k1_tarski(X32),X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

cnf(c_0_31,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,plain,
    ( v1_xboole_0(k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0)) = k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( ~ v1_xboole_0(k2_enumset1(X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_16]),c_0_17])).

cnf(c_0_37,negated_conjecture,
    ( ~ r1_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_22]),c_0_16]),c_0_17])).

cnf(c_0_39,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_enumset1(X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( esk4_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_42,negated_conjecture,
    ( esk4_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.10  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.31  % Computer   : n012.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % WCLimit    : 600
% 0.10/0.31  % DateTime   : Tue Dec  1 10:21:52 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.10/0.31  # Version: 2.5pre002
% 0.10/0.32  # No SInE strategy applied
% 0.10/0.32  # Trying AutoSched0 for 299 seconds
% 0.10/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S0U
% 0.10/0.35  # and selection function SelectComplexExceptRRHorn.
% 0.10/0.35  #
% 0.10/0.35  # Preprocessing time       : 0.028 s
% 0.10/0.35  # Presaturation interreduction done
% 0.10/0.35  
% 0.10/0.35  # Proof found!
% 0.10/0.35  # SZS status Theorem
% 0.10/0.35  # SZS output start CNFRefutation
% 0.10/0.35  fof(t25_zfmisc_1, conjecture, ![X1, X2, X3]:~(((r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))&X1!=X2)&X1!=X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 0.10/0.35  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.10/0.35  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.10/0.35  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.10/0.35  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.10/0.35  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.10/0.35  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.10/0.35  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.10/0.35  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.10/0.35  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3]:~(((r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))&X1!=X2)&X1!=X3))), inference(assume_negation,[status(cth)],[t25_zfmisc_1])).
% 0.10/0.35  fof(c_0_10, plain, ![X17, X18, X19, X20, X21, X22, X23, X24]:(((~r2_hidden(X20,X19)|(X20=X17|X20=X18)|X19!=k2_tarski(X17,X18))&((X21!=X17|r2_hidden(X21,X19)|X19!=k2_tarski(X17,X18))&(X21!=X18|r2_hidden(X21,X19)|X19!=k2_tarski(X17,X18))))&(((esk3_3(X22,X23,X24)!=X22|~r2_hidden(esk3_3(X22,X23,X24),X24)|X24=k2_tarski(X22,X23))&(esk3_3(X22,X23,X24)!=X23|~r2_hidden(esk3_3(X22,X23,X24),X24)|X24=k2_tarski(X22,X23)))&(r2_hidden(esk3_3(X22,X23,X24),X24)|(esk3_3(X22,X23,X24)=X22|esk3_3(X22,X23,X24)=X23)|X24=k2_tarski(X22,X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.10/0.35  fof(c_0_11, plain, ![X27, X28]:k1_enumset1(X27,X27,X28)=k2_tarski(X27,X28), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.10/0.35  fof(c_0_12, plain, ![X29, X30, X31]:k2_enumset1(X29,X29,X30,X31)=k1_enumset1(X29,X30,X31), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.10/0.35  fof(c_0_13, negated_conjecture, ((r1_tarski(k1_tarski(esk4_0),k2_tarski(esk5_0,esk6_0))&esk4_0!=esk5_0)&esk4_0!=esk6_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.10/0.35  fof(c_0_14, plain, ![X26]:k2_tarski(X26,X26)=k1_tarski(X26), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.10/0.35  cnf(c_0_15, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.10/0.35  cnf(c_0_16, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.10/0.35  cnf(c_0_17, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.10/0.35  fof(c_0_18, plain, ![X9, X10, X12, X13, X14]:((r1_xboole_0(X9,X10)|r2_hidden(esk2_2(X9,X10),k3_xboole_0(X9,X10)))&(~r2_hidden(X14,k3_xboole_0(X12,X13))|~r1_xboole_0(X12,X13))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.10/0.35  fof(c_0_19, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.10/0.35  fof(c_0_20, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k3_xboole_0(X15,X16)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.10/0.35  cnf(c_0_21, negated_conjecture, (r1_tarski(k1_tarski(esk4_0),k2_tarski(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.10/0.35  cnf(c_0_22, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.10/0.35  cnf(c_0_23, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 0.10/0.35  cnf(c_0_24, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.10/0.35  cnf(c_0_25, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.10/0.35  cnf(c_0_26, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.10/0.35  cnf(c_0_27, negated_conjecture, (r1_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_16]), c_0_16]), c_0_17]), c_0_17])).
% 0.10/0.35  cnf(c_0_28, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.10/0.35  cnf(c_0_29, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_23])])).
% 0.10/0.35  fof(c_0_30, plain, ![X32, X33]:(r2_hidden(X32,X33)|r1_xboole_0(k1_tarski(X32),X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.10/0.35  cnf(c_0_31, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.10/0.35  cnf(c_0_32, plain, (v1_xboole_0(k3_xboole_0(X1,X2))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.10/0.35  cnf(c_0_33, negated_conjecture, (k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0))=k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.10/0.35  cnf(c_0_34, plain, (~v1_xboole_0(k2_enumset1(X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.10/0.35  cnf(c_0_35, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.10/0.35  cnf(c_0_36, plain, (X1=X4|X1=X3|X2!=k2_enumset1(X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_16]), c_0_17])).
% 0.10/0.35  cnf(c_0_37, negated_conjecture, (~r1_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.10/0.35  cnf(c_0_38, plain, (r2_hidden(X1,X2)|r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_22]), c_0_16]), c_0_17])).
% 0.10/0.35  cnf(c_0_39, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_enumset1(X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_36])).
% 0.10/0.35  cnf(c_0_40, negated_conjecture, (r2_hidden(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.10/0.35  cnf(c_0_41, negated_conjecture, (esk4_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.10/0.35  cnf(c_0_42, negated_conjecture, (esk4_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.10/0.35  cnf(c_0_43, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_42]), ['proof']).
% 0.10/0.35  # SZS output end CNFRefutation
% 0.10/0.35  # Proof object total steps             : 44
% 0.10/0.35  # Proof object clause steps            : 25
% 0.10/0.35  # Proof object formula steps           : 19
% 0.10/0.35  # Proof object conjectures             : 11
% 0.10/0.35  # Proof object clause conjectures      : 8
% 0.10/0.35  # Proof object formula conjectures     : 3
% 0.10/0.35  # Proof object initial clauses used    : 13
% 0.10/0.35  # Proof object initial formulas used   : 9
% 0.10/0.35  # Proof object generating inferences   : 6
% 0.10/0.35  # Proof object simplifying inferences  : 18
% 0.10/0.35  # Training examples: 0 positive, 0 negative
% 0.10/0.35  # Parsed axioms                        : 9
% 0.10/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.10/0.35  # Initial clauses                      : 18
% 0.10/0.35  # Removed in clause preprocessing      : 3
% 0.10/0.35  # Initial clauses in saturation        : 15
% 0.10/0.35  # Processed clauses                    : 36
% 0.10/0.35  # ...of these trivial                  : 0
% 0.10/0.35  # ...subsumed                          : 1
% 0.10/0.35  # ...remaining for further processing  : 35
% 0.10/0.35  # Other redundant clauses eliminated   : 5
% 0.10/0.35  # Clauses deleted for lack of memory   : 0
% 0.10/0.35  # Backward-subsumed                    : 0
% 0.10/0.35  # Backward-rewritten                   : 0
% 0.10/0.35  # Generated clauses                    : 15
% 0.10/0.35  # ...of the previous two non-trivial   : 13
% 0.10/0.35  # Contextual simplify-reflections      : 0
% 0.10/0.35  # Paramodulations                      : 12
% 0.10/0.35  # Factorizations                       : 0
% 0.10/0.35  # Equation resolutions                 : 5
% 0.10/0.35  # Propositional unsat checks           : 0
% 0.10/0.35  #    Propositional check models        : 0
% 0.10/0.35  #    Propositional check unsatisfiable : 0
% 0.10/0.35  #    Propositional clauses             : 0
% 0.10/0.35  #    Propositional clauses after purity: 0
% 0.10/0.35  #    Propositional unsat core size     : 0
% 0.10/0.35  #    Propositional preprocessing time  : 0.000
% 0.10/0.35  #    Propositional encoding time       : 0.000
% 0.10/0.35  #    Propositional solver time         : 0.000
% 0.10/0.35  #    Success case prop preproc time    : 0.000
% 0.10/0.35  #    Success case prop encoding time   : 0.000
% 0.10/0.35  #    Success case prop solver time     : 0.000
% 0.10/0.35  # Current number of processed clauses  : 17
% 0.10/0.35  #    Positive orientable unit clauses  : 5
% 0.10/0.35  #    Positive unorientable unit clauses: 0
% 0.10/0.35  #    Negative unit clauses             : 4
% 0.10/0.35  #    Non-unit-clauses                  : 8
% 0.10/0.35  # Current number of unprocessed clauses: 6
% 0.10/0.35  # ...number of literals in the above   : 16
% 0.10/0.35  # Current number of archived formulas  : 0
% 0.10/0.35  # Current number of archived clauses   : 18
% 0.10/0.35  # Clause-clause subsumption calls (NU) : 11
% 0.10/0.35  # Rec. Clause-clause subsumption calls : 9
% 0.10/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.10/0.35  # Unit Clause-clause subsumption calls : 6
% 0.10/0.35  # Rewrite failures with RHS unbound    : 0
% 0.10/0.35  # BW rewrite match attempts            : 5
% 0.10/0.35  # BW rewrite match successes           : 0
% 0.10/0.35  # Condensation attempts                : 0
% 0.10/0.35  # Condensation successes               : 0
% 0.10/0.35  # Termbank termtop insertions          : 1215
% 0.10/0.35  
% 0.10/0.35  # -------------------------------------------------
% 0.10/0.35  # User time                : 0.030 s
% 0.10/0.35  # System time              : 0.003 s
% 0.10/0.35  # Total time               : 0.032 s
% 0.10/0.35  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
