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
% DateTime   : Thu Dec  3 10:38:08 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 496 expanded)
%              Number of clauses        :   32 ( 202 expanded)
%              Number of leaves         :    9 ( 144 expanded)
%              Depth                    :   12
%              Number of atoms          :  115 ( 929 expanded)
%              Number of equality atoms :   57 ( 517 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t20_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(c_0_9,plain,(
    ! [X27,X28] :
      ( r2_hidden(X27,X28)
      | r1_xboole_0(k1_tarski(X27),X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

fof(c_0_10,plain,(
    ! [X21] : k2_tarski(X21,X21) = k1_tarski(X21) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_11,plain,(
    ! [X22,X23] : k1_enumset1(X22,X22,X23) = k2_tarski(X22,X23) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X24,X25,X26] : k2_enumset1(X24,X24,X25,X26) = k1_enumset1(X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_13,plain,(
    ! [X4,X5,X7,X8,X9] :
      ( ( r2_hidden(esk1_2(X4,X5),X4)
        | r1_xboole_0(X4,X5) )
      & ( r2_hidden(esk1_2(X4,X5),X5)
        | r1_xboole_0(X4,X5) )
      & ( ~ r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | ~ r1_xboole_0(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
      <=> X1 != X2 ) ),
    inference(assume_negation,[status(cth)],[t20_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X12,X13] :
      ( ( ~ r1_xboole_0(X12,X13)
        | k4_xboole_0(X12,X13) = X12 )
      & ( k4_xboole_0(X12,X13) != X12
        | r1_xboole_0(X12,X13) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_22,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X3,k2_enumset1(X1,X1,X1,X1))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_25,plain,(
    ! [X14,X15,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X16,X15)
        | X16 = X14
        | X15 != k1_tarski(X14) )
      & ( X17 != X14
        | r2_hidden(X17,X15)
        | X15 != k1_tarski(X14) )
      & ( ~ r2_hidden(esk2_2(X18,X19),X19)
        | esk2_2(X18,X19) != X18
        | X19 = k1_tarski(X18) )
      & ( r2_hidden(esk2_2(X18,X19),X19)
        | esk2_2(X18,X19) = X18
        | X19 = k1_tarski(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_26,negated_conjecture,
    ( ( k4_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0)) != k1_tarski(esk3_0)
      | esk3_0 = esk4_0 )
    & ( k4_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0)) = k1_tarski(esk3_0)
      | esk3_0 != esk4_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(X2,X3)
    | ~ r2_hidden(esk1_2(X2,X3),k2_enumset1(X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_31,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( esk3_0 = esk4_0
    | k4_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0)) != k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_15]),c_0_16]),c_0_17])).

cnf(c_0_36,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0)) = k1_tarski(esk3_0)
    | esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( esk4_0 = esk3_0
    | k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))) != k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_15]),c_0_15]),c_0_15]),c_0_16]),c_0_16]),c_0_16]),c_0_28]),c_0_17]),c_0_17]),c_0_17]),c_0_17])).

cnf(c_0_38,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) = X1
    | r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_40,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_41,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))) = k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)
    | esk4_0 != esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_15]),c_0_15]),c_0_15]),c_0_16]),c_0_16]),c_0_16]),c_0_28]),c_0_17]),c_0_17]),c_0_17]),c_0_17])).

cnf(c_0_42,negated_conjecture,
    ( esk4_0 = esk3_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != X1 ),
    inference(rw,[status(thm)],[c_0_40,c_0_28])).

cnf(c_0_44,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))) = k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42])])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_46,negated_conjecture,
    ( r1_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_15]),c_0_16]),c_0_17])).

cnf(c_0_48,negated_conjecture,
    ( ~ r2_hidden(X1,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_46])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_47])])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_48,c_0_49]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:51:50 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.13/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.13/0.36  # and selection function SelectCQIArNpEqFirst.
% 0.13/0.36  #
% 0.13/0.36  # Preprocessing time       : 0.027 s
% 0.13/0.36  # Presaturation interreduction done
% 0.13/0.36  
% 0.13/0.36  # Proof found!
% 0.13/0.36  # SZS status Theorem
% 0.13/0.36  # SZS output start CNFRefutation
% 0.13/0.36  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.13/0.36  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.36  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.36  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.36  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.13/0.36  fof(t20_zfmisc_1, conjecture, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.13/0.36  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.13/0.36  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.36  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.13/0.36  fof(c_0_9, plain, ![X27, X28]:(r2_hidden(X27,X28)|r1_xboole_0(k1_tarski(X27),X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.13/0.36  fof(c_0_10, plain, ![X21]:k2_tarski(X21,X21)=k1_tarski(X21), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.36  fof(c_0_11, plain, ![X22, X23]:k1_enumset1(X22,X22,X23)=k2_tarski(X22,X23), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.36  fof(c_0_12, plain, ![X24, X25, X26]:k2_enumset1(X24,X24,X25,X26)=k1_enumset1(X24,X25,X26), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.36  fof(c_0_13, plain, ![X4, X5, X7, X8, X9]:(((r2_hidden(esk1_2(X4,X5),X4)|r1_xboole_0(X4,X5))&(r2_hidden(esk1_2(X4,X5),X5)|r1_xboole_0(X4,X5)))&(~r2_hidden(X9,X7)|~r2_hidden(X9,X8)|~r1_xboole_0(X7,X8))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.13/0.36  cnf(c_0_14, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.36  cnf(c_0_15, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.36  cnf(c_0_16, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.36  cnf(c_0_17, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.36  cnf(c_0_18, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.36  cnf(c_0_19, plain, (r2_hidden(X1,X2)|r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17])).
% 0.13/0.36  fof(c_0_20, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2)), inference(assume_negation,[status(cth)],[t20_zfmisc_1])).
% 0.13/0.36  fof(c_0_21, plain, ![X12, X13]:((~r1_xboole_0(X12,X13)|k4_xboole_0(X12,X13)=X12)&(k4_xboole_0(X12,X13)!=X12|r1_xboole_0(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.13/0.36  fof(c_0_22, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.36  cnf(c_0_23, plain, (r2_hidden(X1,X2)|~r2_hidden(X3,k2_enumset1(X1,X1,X1,X1))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.36  cnf(c_0_24, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.36  fof(c_0_25, plain, ![X14, X15, X16, X17, X18, X19]:(((~r2_hidden(X16,X15)|X16=X14|X15!=k1_tarski(X14))&(X17!=X14|r2_hidden(X17,X15)|X15!=k1_tarski(X14)))&((~r2_hidden(esk2_2(X18,X19),X19)|esk2_2(X18,X19)!=X18|X19=k1_tarski(X18))&(r2_hidden(esk2_2(X18,X19),X19)|esk2_2(X18,X19)=X18|X19=k1_tarski(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.13/0.36  fof(c_0_26, negated_conjecture, ((k4_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0))!=k1_tarski(esk3_0)|esk3_0=esk4_0)&(k4_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0))=k1_tarski(esk3_0)|esk3_0!=esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.13/0.36  cnf(c_0_27, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.36  cnf(c_0_28, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.36  cnf(c_0_29, plain, (r2_hidden(X1,X2)|r1_xboole_0(X2,X3)|~r2_hidden(esk1_2(X2,X3),k2_enumset1(X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.36  cnf(c_0_30, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.36  cnf(c_0_31, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.36  cnf(c_0_32, negated_conjecture, (esk3_0=esk4_0|k4_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0))!=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.36  cnf(c_0_33, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.36  cnf(c_0_34, plain, (r2_hidden(X1,X2)|r1_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.13/0.36  cnf(c_0_35, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_15]), c_0_16]), c_0_17])).
% 0.13/0.36  cnf(c_0_36, negated_conjecture, (k4_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0))=k1_tarski(esk3_0)|esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.36  cnf(c_0_37, negated_conjecture, (esk4_0=esk3_0|k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))!=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_15]), c_0_15]), c_0_15]), c_0_16]), c_0_16]), c_0_16]), c_0_28]), c_0_17]), c_0_17]), c_0_17]), c_0_17])).
% 0.13/0.36  cnf(c_0_38, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))=X1|r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.13/0.36  cnf(c_0_39, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_35])).
% 0.13/0.36  cnf(c_0_40, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.36  cnf(c_0_41, negated_conjecture, (k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)|esk4_0!=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_15]), c_0_15]), c_0_15]), c_0_16]), c_0_16]), c_0_16]), c_0_28]), c_0_17]), c_0_17]), c_0_17]), c_0_17])).
% 0.13/0.36  cnf(c_0_42, negated_conjecture, (esk4_0=esk3_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.13/0.36  cnf(c_0_43, plain, (r1_xboole_0(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=X1), inference(rw,[status(thm)],[c_0_40, c_0_28])).
% 0.13/0.36  cnf(c_0_44, negated_conjecture, (k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)))=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42])])).
% 0.13/0.36  cnf(c_0_45, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.36  cnf(c_0_46, negated_conjecture, (r1_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.13/0.36  cnf(c_0_47, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_15]), c_0_16]), c_0_17])).
% 0.13/0.36  cnf(c_0_48, negated_conjecture, (~r2_hidden(X1,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_18, c_0_46])).
% 0.13/0.36  cnf(c_0_49, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_47])])).
% 0.13/0.36  cnf(c_0_50, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_48, c_0_49]), ['proof']).
% 0.13/0.36  # SZS output end CNFRefutation
% 0.13/0.36  # Proof object total steps             : 51
% 0.13/0.36  # Proof object clause steps            : 32
% 0.13/0.36  # Proof object formula steps           : 19
% 0.13/0.36  # Proof object conjectures             : 12
% 0.13/0.36  # Proof object clause conjectures      : 9
% 0.13/0.36  # Proof object formula conjectures     : 3
% 0.13/0.36  # Proof object initial clauses used    : 14
% 0.13/0.36  # Proof object initial formulas used   : 9
% 0.13/0.36  # Proof object generating inferences   : 8
% 0.13/0.36  # Proof object simplifying inferences  : 43
% 0.13/0.36  # Training examples: 0 positive, 0 negative
% 0.13/0.36  # Parsed axioms                        : 9
% 0.13/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.36  # Initial clauses                      : 16
% 0.13/0.36  # Removed in clause preprocessing      : 4
% 0.13/0.36  # Initial clauses in saturation        : 12
% 0.13/0.36  # Processed clauses                    : 52
% 0.13/0.36  # ...of these trivial                  : 0
% 0.13/0.36  # ...subsumed                          : 7
% 0.13/0.36  # ...remaining for further processing  : 45
% 0.13/0.36  # Other redundant clauses eliminated   : 6
% 0.13/0.36  # Clauses deleted for lack of memory   : 0
% 0.13/0.36  # Backward-subsumed                    : 0
% 0.13/0.36  # Backward-rewritten                   : 5
% 0.13/0.36  # Generated clauses                    : 140
% 0.13/0.36  # ...of the previous two non-trivial   : 127
% 0.13/0.36  # Contextual simplify-reflections      : 1
% 0.13/0.36  # Paramodulations                      : 135
% 0.13/0.36  # Factorizations                       : 0
% 0.13/0.36  # Equation resolutions                 : 6
% 0.13/0.36  # Propositional unsat checks           : 0
% 0.13/0.36  #    Propositional check models        : 0
% 0.13/0.36  #    Propositional check unsatisfiable : 0
% 0.13/0.36  #    Propositional clauses             : 0
% 0.13/0.36  #    Propositional clauses after purity: 0
% 0.13/0.36  #    Propositional unsat core size     : 0
% 0.13/0.36  #    Propositional preprocessing time  : 0.000
% 0.13/0.36  #    Propositional encoding time       : 0.000
% 0.13/0.36  #    Propositional solver time         : 0.000
% 0.13/0.36  #    Success case prop preproc time    : 0.000
% 0.13/0.36  #    Success case prop encoding time   : 0.000
% 0.13/0.36  #    Success case prop solver time     : 0.000
% 0.13/0.36  # Current number of processed clauses  : 26
% 0.13/0.36  #    Positive orientable unit clauses  : 4
% 0.13/0.36  #    Positive unorientable unit clauses: 0
% 0.13/0.36  #    Negative unit clauses             : 1
% 0.13/0.36  #    Non-unit-clauses                  : 21
% 0.13/0.36  # Current number of unprocessed clauses: 93
% 0.13/0.36  # ...number of literals in the above   : 391
% 0.13/0.36  # Current number of archived formulas  : 0
% 0.13/0.36  # Current number of archived clauses   : 21
% 0.13/0.36  # Clause-clause subsumption calls (NU) : 81
% 0.13/0.36  # Rec. Clause-clause subsumption calls : 69
% 0.13/0.36  # Non-unit clause-clause subsumptions  : 8
% 0.13/0.36  # Unit Clause-clause subsumption calls : 0
% 0.13/0.36  # Rewrite failures with RHS unbound    : 0
% 0.13/0.36  # BW rewrite match attempts            : 2
% 0.13/0.36  # BW rewrite match successes           : 1
% 0.13/0.36  # Condensation attempts                : 0
% 0.13/0.36  # Condensation successes               : 0
% 0.13/0.36  # Termbank termtop insertions          : 3100
% 0.13/0.36  
% 0.13/0.36  # -------------------------------------------------
% 0.13/0.36  # User time                : 0.030 s
% 0.13/0.36  # System time              : 0.005 s
% 0.13/0.36  # Total time               : 0.035 s
% 0.13/0.36  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
