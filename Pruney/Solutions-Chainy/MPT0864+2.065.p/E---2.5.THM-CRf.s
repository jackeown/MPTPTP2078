%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:27 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 122 expanded)
%              Number of clauses        :   31 (  55 expanded)
%              Number of leaves         :   10 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  100 ( 227 expanded)
%              Number of equality atoms :   73 ( 178 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   13 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t20_mcart_1,conjecture,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(t35_zfmisc_1,axiom,(
    ! [X1,X2] : k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t42_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_tarski(X2,X3))
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_zfmisc_1)).

fof(t135_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X1,X2))
        | r1_tarski(X1,k2_zfmisc_1(X2,X1)) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(l22_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(t63_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k3_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
     => r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_zfmisc_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t50_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
       => ( X1 != k1_mcart_1(X1)
          & X1 != k2_mcart_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t20_mcart_1])).

fof(c_0_11,plain,(
    ! [X43,X44] :
      ( k1_mcart_1(k4_tarski(X43,X44)) = X43
      & k2_mcart_1(k4_tarski(X43,X44)) = X44 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

fof(c_0_12,negated_conjecture,
    ( esk4_0 = k4_tarski(esk5_0,esk6_0)
    & ( esk4_0 = k1_mcart_1(esk4_0)
      | esk4_0 = k2_mcart_1(esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_13,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( esk4_0 = k4_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X21,X22] : k2_zfmisc_1(k1_tarski(X21),k1_tarski(X22)) = k1_tarski(k4_tarski(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t35_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X6] : k2_tarski(X6,X6) = k1_tarski(X6) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_17,negated_conjecture,
    ( esk4_0 = k1_mcart_1(esk4_0)
    | esk4_0 = k2_mcart_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( k1_mcart_1(esk4_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_20,plain,(
    ! [X23,X24,X25] :
      ( ( ~ r1_tarski(X23,k2_tarski(X24,X25))
        | X23 = k1_xboole_0
        | X23 = k1_tarski(X24)
        | X23 = k1_tarski(X25)
        | X23 = k2_tarski(X24,X25) )
      & ( X23 != k1_xboole_0
        | r1_tarski(X23,k2_tarski(X24,X25)) )
      & ( X23 != k1_tarski(X24)
        | r1_tarski(X23,k2_tarski(X24,X25)) )
      & ( X23 != k1_tarski(X25)
        | r1_tarski(X23,k2_tarski(X24,X25)) )
      & ( X23 != k2_tarski(X24,X25)
        | r1_tarski(X23,k2_tarski(X24,X25)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t42_zfmisc_1])])])).

fof(c_0_21,plain,(
    ! [X19,X20] :
      ( ( ~ r1_tarski(X19,k2_zfmisc_1(X19,X20))
        | X19 = k1_xboole_0 )
      & ( ~ r1_tarski(X19,k2_zfmisc_1(X20,X19))
        | X19 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).

cnf(c_0_22,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( k2_mcart_1(esk4_0) = esk4_0
    | esk5_0 = esk4_0 ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( k2_mcart_1(esk4_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_14])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,k2_tarski(X2,X3))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X7,X8] :
      ( ~ r2_hidden(X7,X8)
      | k2_xboole_0(k1_tarski(X7),X8) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).

fof(c_0_28,plain,(
    ! [X29,X30,X31] :
      ( k3_xboole_0(k2_tarski(X29,X30),X31) != k2_tarski(X29,X30)
      | r2_hidden(X29,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_zfmisc_1])])).

fof(c_0_29,plain,(
    ! [X5] : k3_xboole_0(X5,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_30,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X2,X2)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_23]),c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( esk5_0 = esk4_0
    | esk6_0 = esk4_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k2_tarski(X2,X3))
    | X1 != k2_tarski(X2,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_23])).

fof(c_0_34,plain,(
    ! [X26,X27,X28] : k2_xboole_0(k2_tarski(X26,X27),X28) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t50_zfmisc_1])).

cnf(c_0_35,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X3)
    | k3_xboole_0(k2_tarski(X1,X2),X3) != k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( k2_tarski(X1,X1) = k1_xboole_0
    | ~ r1_tarski(k2_tarski(X1,X1),k2_tarski(k4_tarski(X2,X1),k4_tarski(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( k4_tarski(esk5_0,esk4_0) = esk4_0
    | esk5_0 = esk4_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_32])).

cnf(c_0_40,plain,
    ( r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( k2_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k2_xboole_0(k2_tarski(X1,X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_23])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k1_xboole_0)
    | k2_tarski(X1,X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( k2_tarski(esk4_0,esk4_0) = k1_xboole_0
    | esk5_0 = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42])])).

cnf(c_0_46,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_47,negated_conjecture,
    ( esk5_0 = esk4_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_48,plain,
    ( k2_tarski(X1,X1) = k1_xboole_0
    | ~ r1_tarski(k2_tarski(X1,X1),k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_31])).

cnf(c_0_49,negated_conjecture,
    ( k4_tarski(esk4_0,esk6_0) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_14,c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( k2_tarski(esk4_0,esk4_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_40])])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_50]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:53:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.028 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t20_mcart_1, conjecture, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.20/0.39  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.20/0.39  fof(t35_zfmisc_1, axiom, ![X1, X2]:k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 0.20/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.39  fof(t42_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_tarski(X2,X3))<=>~((((X1!=k1_xboole_0&X1!=k1_tarski(X2))&X1!=k1_tarski(X3))&X1!=k2_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_zfmisc_1)).
% 0.20/0.39  fof(t135_zfmisc_1, axiom, ![X1, X2]:((r1_tarski(X1,k2_zfmisc_1(X1,X2))|r1_tarski(X1,k2_zfmisc_1(X2,X1)))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 0.20/0.39  fof(l22_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 0.20/0.39  fof(t63_zfmisc_1, axiom, ![X1, X2, X3]:(k3_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)=>r2_hidden(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 0.20/0.39  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.20/0.39  fof(t50_zfmisc_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 0.20/0.39  fof(c_0_10, negated_conjecture, ~(![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1)))), inference(assume_negation,[status(cth)],[t20_mcart_1])).
% 0.20/0.39  fof(c_0_11, plain, ![X43, X44]:(k1_mcart_1(k4_tarski(X43,X44))=X43&k2_mcart_1(k4_tarski(X43,X44))=X44), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.20/0.39  fof(c_0_12, negated_conjecture, (esk4_0=k4_tarski(esk5_0,esk6_0)&(esk4_0=k1_mcart_1(esk4_0)|esk4_0=k2_mcart_1(esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.20/0.39  cnf(c_0_13, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_14, negated_conjecture, (esk4_0=k4_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  fof(c_0_15, plain, ![X21, X22]:k2_zfmisc_1(k1_tarski(X21),k1_tarski(X22))=k1_tarski(k4_tarski(X21,X22)), inference(variable_rename,[status(thm)],[t35_zfmisc_1])).
% 0.20/0.39  fof(c_0_16, plain, ![X6]:k2_tarski(X6,X6)=k1_tarski(X6), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.39  cnf(c_0_17, negated_conjecture, (esk4_0=k1_mcart_1(esk4_0)|esk4_0=k2_mcart_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_18, negated_conjecture, (k1_mcart_1(esk4_0)=esk5_0), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.39  cnf(c_0_19, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  fof(c_0_20, plain, ![X23, X24, X25]:((~r1_tarski(X23,k2_tarski(X24,X25))|(X23=k1_xboole_0|X23=k1_tarski(X24)|X23=k1_tarski(X25)|X23=k2_tarski(X24,X25)))&((((X23!=k1_xboole_0|r1_tarski(X23,k2_tarski(X24,X25)))&(X23!=k1_tarski(X24)|r1_tarski(X23,k2_tarski(X24,X25))))&(X23!=k1_tarski(X25)|r1_tarski(X23,k2_tarski(X24,X25))))&(X23!=k2_tarski(X24,X25)|r1_tarski(X23,k2_tarski(X24,X25))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t42_zfmisc_1])])])).
% 0.20/0.39  fof(c_0_21, plain, ![X19, X20]:((~r1_tarski(X19,k2_zfmisc_1(X19,X20))|X19=k1_xboole_0)&(~r1_tarski(X19,k2_zfmisc_1(X20,X19))|X19=k1_xboole_0)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).
% 0.20/0.39  cnf(c_0_22, plain, (k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_23, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_24, negated_conjecture, (k2_mcart_1(esk4_0)=esk4_0|esk5_0=esk4_0), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.39  cnf(c_0_25, negated_conjecture, (k2_mcart_1(esk4_0)=esk6_0), inference(spm,[status(thm)],[c_0_19, c_0_14])).
% 0.20/0.39  cnf(c_0_26, plain, (r1_tarski(X1,k2_tarski(X2,X3))|X1!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  fof(c_0_27, plain, ![X7, X8]:(~r2_hidden(X7,X8)|k2_xboole_0(k1_tarski(X7),X8)=X8), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).
% 0.20/0.39  fof(c_0_28, plain, ![X29, X30, X31]:(k3_xboole_0(k2_tarski(X29,X30),X31)!=k2_tarski(X29,X30)|r2_hidden(X29,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_zfmisc_1])])).
% 0.20/0.39  fof(c_0_29, plain, ![X5]:k3_xboole_0(X5,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.20/0.39  cnf(c_0_30, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.39  cnf(c_0_31, plain, (k2_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X2,X2))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_23]), c_0_23])).
% 0.20/0.39  cnf(c_0_32, negated_conjecture, (esk5_0=esk4_0|esk6_0=esk4_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.39  cnf(c_0_33, plain, (r1_tarski(X1,k2_tarski(X2,X3))|X1!=k2_tarski(X2,X2)), inference(rw,[status(thm)],[c_0_26, c_0_23])).
% 0.20/0.39  fof(c_0_34, plain, ![X26, X27, X28]:k2_xboole_0(k2_tarski(X26,X27),X28)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t50_zfmisc_1])).
% 0.20/0.39  cnf(c_0_35, plain, (k2_xboole_0(k1_tarski(X1),X2)=X2|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  cnf(c_0_36, plain, (r2_hidden(X1,X3)|k3_xboole_0(k2_tarski(X1,X2),X3)!=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.39  cnf(c_0_37, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.39  cnf(c_0_38, plain, (k2_tarski(X1,X1)=k1_xboole_0|~r1_tarski(k2_tarski(X1,X1),k2_tarski(k4_tarski(X2,X1),k4_tarski(X2,X1)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.39  cnf(c_0_39, negated_conjecture, (k4_tarski(esk5_0,esk4_0)=esk4_0|esk5_0=esk4_0), inference(spm,[status(thm)],[c_0_14, c_0_32])).
% 0.20/0.39  cnf(c_0_40, plain, (r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X2))), inference(er,[status(thm)],[c_0_33])).
% 0.20/0.39  cnf(c_0_41, plain, (k2_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.39  cnf(c_0_42, plain, (k2_xboole_0(k2_tarski(X1,X1),X2)=X2|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_35, c_0_23])).
% 0.20/0.39  cnf(c_0_43, plain, (r2_hidden(X1,k1_xboole_0)|k2_tarski(X1,X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.39  cnf(c_0_44, negated_conjecture, (k2_tarski(esk4_0,esk4_0)=k1_xboole_0|esk5_0=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 0.20/0.39  cnf(c_0_45, plain, (~r2_hidden(X1,k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42])])).
% 0.20/0.39  cnf(c_0_46, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.39  cnf(c_0_47, negated_conjecture, (esk5_0=esk4_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])).
% 0.20/0.39  cnf(c_0_48, plain, (k2_tarski(X1,X1)=k1_xboole_0|~r1_tarski(k2_tarski(X1,X1),k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_46, c_0_31])).
% 0.20/0.39  cnf(c_0_49, negated_conjecture, (k4_tarski(esk4_0,esk6_0)=esk4_0), inference(rw,[status(thm)],[c_0_14, c_0_47])).
% 0.20/0.39  cnf(c_0_50, negated_conjecture, (k2_tarski(esk4_0,esk4_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_40])])).
% 0.20/0.39  cnf(c_0_51, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_50]), c_0_45]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 52
% 0.20/0.39  # Proof object clause steps            : 31
% 0.20/0.39  # Proof object formula steps           : 21
% 0.20/0.39  # Proof object conjectures             : 15
% 0.20/0.39  # Proof object clause conjectures      : 12
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 13
% 0.20/0.39  # Proof object initial formulas used   : 10
% 0.20/0.39  # Proof object generating inferences   : 12
% 0.20/0.39  # Proof object simplifying inferences  : 15
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 15
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 32
% 0.20/0.39  # Removed in clause preprocessing      : 1
% 0.20/0.39  # Initial clauses in saturation        : 31
% 0.20/0.39  # Processed clauses                    : 199
% 0.20/0.39  # ...of these trivial                  : 0
% 0.20/0.39  # ...subsumed                          : 71
% 0.20/0.39  # ...remaining for further processing  : 128
% 0.20/0.39  # Other redundant clauses eliminated   : 11
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 7
% 0.20/0.39  # Backward-rewritten                   : 32
% 0.20/0.39  # Generated clauses                    : 329
% 0.20/0.39  # ...of the previous two non-trivial   : 304
% 0.20/0.39  # Contextual simplify-reflections      : 0
% 0.20/0.39  # Paramodulations                      : 318
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 11
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
% 0.20/0.39  # Current number of processed clauses  : 48
% 0.20/0.39  #    Positive orientable unit clauses  : 17
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 2
% 0.20/0.39  #    Non-unit-clauses                  : 29
% 0.20/0.39  # Current number of unprocessed clauses: 130
% 0.20/0.39  # ...number of literals in the above   : 371
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 71
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 666
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 454
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 55
% 0.20/0.39  # Unit Clause-clause subsumption calls : 3
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 9
% 0.20/0.39  # BW rewrite match successes           : 3
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 5557
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.033 s
% 0.20/0.39  # System time              : 0.007 s
% 0.20/0.39  # Total time               : 0.041 s
% 0.20/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
