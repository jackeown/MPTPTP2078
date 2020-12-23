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
% DateTime   : Thu Dec  3 10:45:01 EST 2020

% Result     : Theorem 0.23s
% Output     : CNFRefutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   48 (  85 expanded)
%              Number of clauses        :   29 (  40 expanded)
%              Number of leaves         :    9 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  111 ( 219 expanded)
%              Number of equality atoms :   11 (  27 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t37_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t149_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
        & r2_hidden(X4,X3)
        & r1_xboole_0(X3,X2) )
     => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(t64_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4)
        & r1_xboole_0(X2,X4) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t77_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r1_xboole_0(X1,X2)
        & r1_tarski(X1,X3)
        & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(c_0_9,plain,(
    ! [X9,X10] :
      ( ( r1_tarski(X9,X10)
        | X9 != X10 )
      & ( r1_tarski(X10,X9)
        | X9 != X10 )
      & ( ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X10,X9)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_10,plain,(
    ! [X27,X28] :
      ( ( ~ r1_tarski(k1_tarski(X27),X28)
        | r2_hidden(X27,X28) )
      & ( ~ r2_hidden(X27,X28)
        | r1_tarski(k1_tarski(X27),X28) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_zfmisc_1])])).

fof(c_0_11,plain,(
    ! [X23] : k2_tarski(X23,X23) = k1_tarski(X23) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
          & r2_hidden(X4,X3)
          & r1_xboole_0(X3,X2) )
       => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t149_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X13,X14,X15,X16] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X15,X16)
      | ~ r1_xboole_0(X14,X16)
      | r1_xboole_0(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_xboole_1])])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk1_0,esk2_0),k1_tarski(esk4_0))
    & r2_hidden(esk4_0,esk3_0)
    & r1_xboole_0(esk3_0,esk2_0)
    & ~ r1_xboole_0(k2_xboole_0(esk1_0,esk3_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_18,plain,(
    ! [X11,X12] : k4_xboole_0(X11,k4_xboole_0(X11,X12)) = k3_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_19,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4)
    | ~ r1_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r1_tarski(k2_tarski(X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk1_0,esk2_0),k1_tarski(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(k2_tarski(esk4_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_27,plain,(
    ! [X20,X21,X22] :
      ( r1_xboole_0(X20,X21)
      | ~ r1_tarski(X20,X22)
      | ~ r1_xboole_0(X20,k3_xboole_0(X21,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t77_xboole_1])])])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),k2_tarski(esk4_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_16]),c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r1_xboole_0(k2_tarski(esk4_0,esk4_0),X1)
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_31,plain,(
    ! [X7,X8] :
      ( ~ r1_xboole_0(X7,X8)
      | r1_xboole_0(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_32,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),X1)
    | ~ r1_xboole_0(k2_tarski(esk4_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r1_xboole_0(k2_tarski(esk4_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_35,plain,(
    ! [X17,X18,X19] :
      ( ( r1_xboole_0(X17,k2_xboole_0(X18,X19))
        | ~ r1_xboole_0(X17,X18)
        | ~ r1_xboole_0(X17,X19) )
      & ( r1_xboole_0(X17,X18)
        | ~ r1_xboole_0(X17,k2_xboole_0(X18,X19)) )
      & ( r1_xboole_0(X17,X19)
        | ~ r1_xboole_0(X17,k2_xboole_0(X18,X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_36,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_24])).

cnf(c_0_38,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_30])).

cnf(c_0_41,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_20])).

cnf(c_0_42,negated_conjecture,
    ( r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( r1_xboole_0(esk2_0,k2_xboole_0(X1,esk3_0))
    | ~ r1_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( r1_xboole_0(esk2_0,k2_xboole_0(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(esk1_0,esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_45]),c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.36  % Computer   : n012.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % WCLimit    : 600
% 0.13/0.36  % DateTime   : Tue Dec  1 20:08:37 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  # Version: 2.5pre002
% 0.13/0.37  # No SInE strategy applied
% 0.13/0.37  # Trying AutoSched0 for 299 seconds
% 0.23/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S083N
% 0.23/0.40  # and selection function SelectCQArNT.
% 0.23/0.40  #
% 0.23/0.40  # Preprocessing time       : 0.027 s
% 0.23/0.40  # Presaturation interreduction done
% 0.23/0.40  
% 0.23/0.40  # Proof found!
% 0.23/0.40  # SZS status Theorem
% 0.23/0.40  # SZS output start CNFRefutation
% 0.23/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.23/0.40  fof(t37_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 0.23/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.23/0.40  fof(t149_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 0.23/0.40  fof(t64_xboole_1, axiom, ![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&r1_tarski(X3,X4))&r1_xboole_0(X2,X4))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_xboole_1)).
% 0.23/0.40  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.23/0.40  fof(t77_xboole_1, axiom, ![X1, X2, X3]:~(((~(r1_xboole_0(X1,X2))&r1_tarski(X1,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 0.23/0.40  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.23/0.40  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.23/0.40  fof(c_0_9, plain, ![X9, X10]:(((r1_tarski(X9,X10)|X9!=X10)&(r1_tarski(X10,X9)|X9!=X10))&(~r1_tarski(X9,X10)|~r1_tarski(X10,X9)|X9=X10)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.23/0.40  fof(c_0_10, plain, ![X27, X28]:((~r1_tarski(k1_tarski(X27),X28)|r2_hidden(X27,X28))&(~r2_hidden(X27,X28)|r1_tarski(k1_tarski(X27),X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_zfmisc_1])])).
% 0.23/0.40  fof(c_0_11, plain, ![X23]:k2_tarski(X23,X23)=k1_tarski(X23), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.23/0.40  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t149_zfmisc_1])).
% 0.23/0.40  fof(c_0_13, plain, ![X13, X14, X15, X16]:(~r1_tarski(X13,X14)|~r1_tarski(X15,X16)|~r1_xboole_0(X14,X16)|r1_xboole_0(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_xboole_1])])).
% 0.23/0.40  cnf(c_0_14, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.23/0.40  cnf(c_0_15, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.23/0.40  cnf(c_0_16, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.23/0.40  fof(c_0_17, negated_conjecture, (((r1_tarski(k3_xboole_0(esk1_0,esk2_0),k1_tarski(esk4_0))&r2_hidden(esk4_0,esk3_0))&r1_xboole_0(esk3_0,esk2_0))&~r1_xboole_0(k2_xboole_0(esk1_0,esk3_0),esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.23/0.40  fof(c_0_18, plain, ![X11, X12]:k4_xboole_0(X11,k4_xboole_0(X11,X12))=k3_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.23/0.40  cnf(c_0_19, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)|~r1_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.23/0.40  cnf(c_0_20, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_14])).
% 0.23/0.40  cnf(c_0_21, plain, (r1_tarski(k2_tarski(X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.23/0.40  cnf(c_0_22, negated_conjecture, (r2_hidden(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.23/0.40  cnf(c_0_23, negated_conjecture, (r1_tarski(k3_xboole_0(esk1_0,esk2_0),k1_tarski(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.23/0.40  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.23/0.40  cnf(c_0_25, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,X3)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.23/0.40  cnf(c_0_26, negated_conjecture, (r1_tarski(k2_tarski(esk4_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.23/0.40  fof(c_0_27, plain, ![X20, X21, X22]:(r1_xboole_0(X20,X21)|~r1_tarski(X20,X22)|~r1_xboole_0(X20,k3_xboole_0(X21,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t77_xboole_1])])])).
% 0.23/0.40  cnf(c_0_28, negated_conjecture, (r1_tarski(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),k2_tarski(esk4_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_16]), c_0_24])).
% 0.23/0.41  cnf(c_0_29, negated_conjecture, (r1_xboole_0(k2_tarski(esk4_0,esk4_0),X1)|~r1_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.23/0.41  cnf(c_0_30, negated_conjecture, (r1_xboole_0(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.23/0.41  fof(c_0_31, plain, ![X7, X8]:(~r1_xboole_0(X7,X8)|r1_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.23/0.41  cnf(c_0_32, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,X3)|~r1_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.23/0.41  cnf(c_0_33, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),X1)|~r1_xboole_0(k2_tarski(esk4_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_25, c_0_28])).
% 0.23/0.41  cnf(c_0_34, negated_conjecture, (r1_xboole_0(k2_tarski(esk4_0,esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.23/0.41  fof(c_0_35, plain, ![X17, X18, X19]:((r1_xboole_0(X17,k2_xboole_0(X18,X19))|~r1_xboole_0(X17,X18)|~r1_xboole_0(X17,X19))&((r1_xboole_0(X17,X18)|~r1_xboole_0(X17,k2_xboole_0(X18,X19)))&(r1_xboole_0(X17,X19)|~r1_xboole_0(X17,k2_xboole_0(X18,X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.23/0.41  cnf(c_0_36, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.23/0.41  cnf(c_0_37, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,X3)|~r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_32, c_0_24])).
% 0.23/0.41  cnf(c_0_38, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),esk2_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.23/0.41  cnf(c_0_39, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.23/0.41  cnf(c_0_40, negated_conjecture, (r1_xboole_0(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_36, c_0_30])).
% 0.23/0.41  cnf(c_0_41, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_37, c_0_20])).
% 0.23/0.41  cnf(c_0_42, negated_conjecture, (r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_36, c_0_38])).
% 0.23/0.41  cnf(c_0_43, negated_conjecture, (r1_xboole_0(esk2_0,k2_xboole_0(X1,esk3_0))|~r1_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.23/0.41  cnf(c_0_44, negated_conjecture, (r1_xboole_0(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.23/0.41  cnf(c_0_45, negated_conjecture, (r1_xboole_0(esk2_0,k2_xboole_0(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.23/0.41  cnf(c_0_46, negated_conjecture, (~r1_xboole_0(k2_xboole_0(esk1_0,esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.23/0.41  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_45]), c_0_46]), ['proof']).
% 0.23/0.41  # SZS output end CNFRefutation
% 0.23/0.41  # Proof object total steps             : 48
% 0.23/0.41  # Proof object clause steps            : 29
% 0.23/0.41  # Proof object formula steps           : 19
% 0.23/0.41  # Proof object conjectures             : 19
% 0.23/0.41  # Proof object clause conjectures      : 16
% 0.23/0.41  # Proof object formula conjectures     : 3
% 0.23/0.41  # Proof object initial clauses used    : 12
% 0.23/0.41  # Proof object initial formulas used   : 9
% 0.23/0.41  # Proof object generating inferences   : 13
% 0.23/0.41  # Proof object simplifying inferences  : 6
% 0.23/0.41  # Training examples: 0 positive, 0 negative
% 0.23/0.41  # Parsed axioms                        : 11
% 0.23/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.23/0.41  # Initial clauses                      : 24
% 0.23/0.41  # Removed in clause preprocessing      : 2
% 0.23/0.41  # Initial clauses in saturation        : 22
% 0.23/0.41  # Processed clauses                    : 170
% 0.23/0.41  # ...of these trivial                  : 4
% 0.23/0.41  # ...subsumed                          : 0
% 0.23/0.41  # ...remaining for further processing  : 166
% 0.23/0.41  # Other redundant clauses eliminated   : 6
% 0.23/0.41  # Clauses deleted for lack of memory   : 0
% 0.23/0.41  # Backward-subsumed                    : 0
% 0.23/0.41  # Backward-rewritten                   : 1
% 0.23/0.41  # Generated clauses                    : 547
% 0.23/0.41  # ...of the previous two non-trivial   : 411
% 0.23/0.41  # Contextual simplify-reflections      : 0
% 0.23/0.41  # Paramodulations                      : 540
% 0.23/0.41  # Factorizations                       : 1
% 0.23/0.41  # Equation resolutions                 : 6
% 0.23/0.41  # Propositional unsat checks           : 0
% 0.23/0.41  #    Propositional check models        : 0
% 0.23/0.41  #    Propositional check unsatisfiable : 0
% 0.23/0.41  #    Propositional clauses             : 0
% 0.23/0.41  #    Propositional clauses after purity: 0
% 0.23/0.41  #    Propositional unsat core size     : 0
% 0.23/0.41  #    Propositional preprocessing time  : 0.000
% 0.23/0.41  #    Propositional encoding time       : 0.000
% 0.23/0.41  #    Propositional solver time         : 0.000
% 0.23/0.41  #    Success case prop preproc time    : 0.000
% 0.23/0.41  #    Success case prop encoding time   : 0.000
% 0.23/0.41  #    Success case prop solver time     : 0.000
% 0.23/0.41  # Current number of processed clauses  : 139
% 0.23/0.41  #    Positive orientable unit clauses  : 74
% 0.23/0.41  #    Positive unorientable unit clauses: 0
% 0.23/0.41  #    Negative unit clauses             : 1
% 0.23/0.41  #    Non-unit-clauses                  : 64
% 0.23/0.41  # Current number of unprocessed clauses: 282
% 0.23/0.41  # ...number of literals in the above   : 366
% 0.23/0.41  # Current number of archived formulas  : 0
% 0.23/0.41  # Current number of archived clauses   : 23
% 0.23/0.41  # Clause-clause subsumption calls (NU) : 519
% 0.23/0.41  # Rec. Clause-clause subsumption calls : 442
% 0.23/0.41  # Non-unit clause-clause subsumptions  : 0
% 0.23/0.41  # Unit Clause-clause subsumption calls : 777
% 0.23/0.41  # Rewrite failures with RHS unbound    : 0
% 0.23/0.41  # BW rewrite match attempts            : 41
% 0.23/0.41  # BW rewrite match successes           : 1
% 0.23/0.41  # Condensation attempts                : 0
% 0.23/0.41  # Condensation successes               : 0
% 0.23/0.41  # Termbank termtop insertions          : 8586
% 0.23/0.41  
% 0.23/0.41  # -------------------------------------------------
% 0.23/0.41  # User time                : 0.037 s
% 0.23/0.41  # System time              : 0.005 s
% 0.23/0.41  # Total time               : 0.042 s
% 0.23/0.41  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
