%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:40:58 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 157 expanded)
%              Number of clauses        :   25 (  64 expanded)
%              Number of leaves         :   11 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :   72 ( 193 expanded)
%              Number of equality atoms :   39 ( 148 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t48_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & r2_hidden(X3,X2) )
     => k2_xboole_0(k2_tarski(X1,X3),X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t45_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(c_0_11,plain,(
    ! [X25,X26] : k3_tarski(k2_tarski(X25,X26)) = k2_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X27,X28,X29] :
      ( ( r2_hidden(X27,X29)
        | ~ r1_tarski(k2_tarski(X27,X28),X29) )
      & ( r2_hidden(X28,X29)
        | ~ r1_tarski(k2_tarski(X27,X28),X29) )
      & ( ~ r2_hidden(X27,X29)
        | ~ r2_hidden(X28,X29)
        | r1_tarski(k2_tarski(X27,X28),X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_14,plain,(
    ! [X18,X19,X20] : k2_enumset1(X18,X18,X19,X20) = k1_enumset1(X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_15,plain,(
    ! [X21,X22,X23,X24] : k3_enumset1(X21,X21,X22,X23,X24) = k2_enumset1(X21,X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r2_hidden(X1,X2)
          & r2_hidden(X3,X2) )
       => k2_xboole_0(k2_tarski(X1,X3),X2) = X2 ) ),
    inference(assume_negation,[status(cth)],[t48_zfmisc_1])).

fof(c_0_17,plain,(
    ! [X14,X15] : k2_xboole_0(X14,X15) = k5_xboole_0(k5_xboole_0(X14,X15),k3_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

cnf(c_0_18,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,plain,(
    ! [X9,X10] :
      ( ~ r1_tarski(X9,X10)
      | X10 = k2_xboole_0(X9,k4_xboole_0(X10,X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).

fof(c_0_21,plain,(
    ! [X5,X6] : k4_xboole_0(X5,X6) = k5_xboole_0(X5,k3_xboole_0(X5,X6)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_22,plain,(
    ! [X7,X8] : k2_xboole_0(X7,k4_xboole_0(X8,X7)) = k2_xboole_0(X7,X8) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_23,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_26,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0)
    & r2_hidden(esk3_0,esk2_0)
    & k2_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0) != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_29,plain,(
    ! [X11,X12,X13] : k5_xboole_0(k5_xboole_0(X11,X12),X13) = k5_xboole_0(X11,k5_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_30,plain,
    ( X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_19]),c_0_24]),c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_24]),c_0_25])).

cnf(c_0_37,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( X2 = k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_28]),c_0_31]),c_0_24]),c_0_25])).

cnf(c_0_39,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_28]),c_0_28]),c_0_31]),c_0_24]),c_0_24]),c_0_25]),c_0_25])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,esk3_0),esk2_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,negated_conjecture,
    ( k3_tarski(k3_enumset1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),esk2_0)) != esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_19]),c_0_28]),c_0_24]),c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_43,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k5_xboole_0(esk2_0,k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),esk2_0))) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_43]),c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:15:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S081N
% 0.13/0.37  # and selection function SelectCQArNTNp.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.13/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.37  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.13/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.37  fof(t48_zfmisc_1, conjecture, ![X1, X2, X3]:((r2_hidden(X1,X2)&r2_hidden(X3,X2))=>k2_xboole_0(k2_tarski(X1,X3),X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 0.13/0.37  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.13/0.37  fof(t45_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 0.13/0.37  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.37  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.13/0.37  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.13/0.37  fof(c_0_11, plain, ![X25, X26]:k3_tarski(k2_tarski(X25,X26))=k2_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.13/0.37  fof(c_0_12, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.37  fof(c_0_13, plain, ![X27, X28, X29]:(((r2_hidden(X27,X29)|~r1_tarski(k2_tarski(X27,X28),X29))&(r2_hidden(X28,X29)|~r1_tarski(k2_tarski(X27,X28),X29)))&(~r2_hidden(X27,X29)|~r2_hidden(X28,X29)|r1_tarski(k2_tarski(X27,X28),X29))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.13/0.37  fof(c_0_14, plain, ![X18, X19, X20]:k2_enumset1(X18,X18,X19,X20)=k1_enumset1(X18,X19,X20), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.37  fof(c_0_15, plain, ![X21, X22, X23, X24]:k3_enumset1(X21,X21,X22,X23,X24)=k2_enumset1(X21,X22,X23,X24), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.37  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3]:((r2_hidden(X1,X2)&r2_hidden(X3,X2))=>k2_xboole_0(k2_tarski(X1,X3),X2)=X2)), inference(assume_negation,[status(cth)],[t48_zfmisc_1])).
% 0.13/0.37  fof(c_0_17, plain, ![X14, X15]:k2_xboole_0(X14,X15)=k5_xboole_0(k5_xboole_0(X14,X15),k3_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.13/0.37  cnf(c_0_18, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_19, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  fof(c_0_20, plain, ![X9, X10]:(~r1_tarski(X9,X10)|X10=k2_xboole_0(X9,k4_xboole_0(X10,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).
% 0.13/0.37  fof(c_0_21, plain, ![X5, X6]:k4_xboole_0(X5,X6)=k5_xboole_0(X5,k3_xboole_0(X5,X6)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.37  fof(c_0_22, plain, ![X7, X8]:k2_xboole_0(X7,k4_xboole_0(X8,X7))=k2_xboole_0(X7,X8), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.13/0.37  cnf(c_0_23, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_24, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_25, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  fof(c_0_26, negated_conjecture, ((r2_hidden(esk1_0,esk2_0)&r2_hidden(esk3_0,esk2_0))&k2_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0)!=esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.13/0.37  cnf(c_0_27, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.37  cnf(c_0_28, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.37  fof(c_0_29, plain, ![X11, X12, X13]:k5_xboole_0(k5_xboole_0(X11,X12),X13)=k5_xboole_0(X11,k5_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.13/0.37  cnf(c_0_30, plain, (X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.37  cnf(c_0_31, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.37  cnf(c_0_32, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.37  cnf(c_0_33, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_19]), c_0_24]), c_0_25])).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (r2_hidden(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.37  cnf(c_0_35, negated_conjecture, (k2_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0)!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.37  cnf(c_0_36, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_24]), c_0_25])).
% 0.13/0.37  cnf(c_0_37, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.37  cnf(c_0_38, plain, (X2=k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_28]), c_0_31]), c_0_24]), c_0_25])).
% 0.13/0.37  cnf(c_0_39, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_28]), c_0_28]), c_0_31]), c_0_24]), c_0_24]), c_0_25]), c_0_25])).
% 0.13/0.37  cnf(c_0_40, negated_conjecture, (r1_tarski(k3_enumset1(X1,X1,X1,X1,esk3_0),esk2_0)|~r2_hidden(X1,esk2_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.13/0.37  cnf(c_0_41, negated_conjecture, (r2_hidden(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.37  cnf(c_0_42, negated_conjecture, (k3_tarski(k3_enumset1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),esk2_0))!=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_19]), c_0_28]), c_0_24]), c_0_24]), c_0_24]), c_0_25]), c_0_25]), c_0_25]), c_0_25])).
% 0.13/0.37  cnf(c_0_43, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.37  cnf(c_0_44, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.37  cnf(c_0_45, negated_conjecture, (r1_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.13/0.37  cnf(c_0_46, negated_conjecture, (k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k5_xboole_0(esk2_0,k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),esk2_0)))!=esk2_0), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.13/0.37  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_43]), c_0_46]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 48
% 0.13/0.37  # Proof object clause steps            : 25
% 0.13/0.37  # Proof object formula steps           : 23
% 0.13/0.37  # Proof object conjectures             : 11
% 0.13/0.37  # Proof object clause conjectures      : 8
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 13
% 0.13/0.37  # Proof object initial formulas used   : 11
% 0.13/0.37  # Proof object generating inferences   : 3
% 0.13/0.37  # Proof object simplifying inferences  : 32
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 11
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 15
% 0.13/0.37  # Removed in clause preprocessing      : 5
% 0.13/0.37  # Initial clauses in saturation        : 10
% 0.13/0.37  # Processed clauses                    : 24
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 24
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 2
% 0.13/0.37  # Generated clauses                    : 12
% 0.13/0.37  # ...of the previous two non-trivial   : 8
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 12
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 12
% 0.13/0.37  #    Positive orientable unit clauses  : 6
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 1
% 0.13/0.37  #    Non-unit-clauses                  : 5
% 0.13/0.37  # Current number of unprocessed clauses: 4
% 0.13/0.37  # ...number of literals in the above   : 5
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 17
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 4
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 4
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 1
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 5
% 0.13/0.37  # BW rewrite match successes           : 4
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1010
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.026 s
% 0.13/0.37  # System time              : 0.005 s
% 0.13/0.37  # Total time               : 0.031 s
% 0.13/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
