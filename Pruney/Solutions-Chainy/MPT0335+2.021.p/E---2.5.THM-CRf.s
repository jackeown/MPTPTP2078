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
% DateTime   : Thu Dec  3 10:44:43 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   49 (  92 expanded)
%              Number of clauses        :   30 (  41 expanded)
%              Number of leaves         :    9 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :   87 ( 191 expanded)
%              Number of equality atoms :   35 (  82 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t148_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & k3_xboole_0(X2,X3) = k1_tarski(X4)
        & r2_hidden(X4,X1) )
     => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t46_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t23_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(X1,X2)
          & k3_xboole_0(X2,X3) = k1_tarski(X4)
          & r2_hidden(X4,X1) )
       => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    inference(assume_negation,[status(cth)],[t148_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_11,plain,(
    ! [X11,X12] : r1_tarski(k3_xboole_0(X11,X12),X11) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_12,plain,(
    ! [X28,X29] :
      ( ~ r2_hidden(X28,X29)
      | k2_xboole_0(k1_tarski(X28),X29) = X29 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_zfmisc_1])])).

fof(c_0_13,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & k3_xboole_0(esk2_0,esk3_0) = k1_tarski(esk4_0)
    & r2_hidden(esk4_0,esk1_0)
    & k3_xboole_0(esk1_0,esk3_0) != k1_tarski(esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_14,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X13,X15)
      | r1_tarski(X13,k3_xboole_0(X14,X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk3_0) = k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X26,X27] : r1_tarski(X26,k2_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_21,plain,(
    ! [X20,X21,X22] : k3_xboole_0(X20,k2_xboole_0(X21,X22)) = k2_xboole_0(k3_xboole_0(X20,X21),k3_xboole_0(X20,X22)) ),
    inference(variable_rename,[status(thm)],[t23_xboole_1])).

fof(c_0_22,plain,(
    ! [X9,X10] :
      ( ~ r1_tarski(X9,X10)
      | k2_xboole_0(X9,X10) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( k2_xboole_0(k3_xboole_0(esk2_0,esk3_0),X1) = X1
    | ~ r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_33,negated_conjecture,
    ( k2_xboole_0(k3_xboole_0(esk2_0,esk3_0),esk1_0) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_34,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_35,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = X1
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_24])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk2_0,esk3_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_33])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,esk1_0),k3_xboole_0(X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( k3_xboole_0(k3_xboole_0(esk2_0,esk3_0),k3_xboole_0(X1,esk1_0)) = k3_xboole_0(esk2_0,esk3_0)
    | ~ r1_tarski(k3_xboole_0(esk2_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,esk1_0),k3_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk3_0) != k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_45,negated_conjecture,
    ( k3_xboole_0(k3_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk2_0,esk3_0)) = k3_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_39]),c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk1_0,X1),k3_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk3_0) != k3_xboole_0(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_44,c_0_19])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_45]),c_0_46])]),c_0_47]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:34:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.17/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.17/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.17/0.37  #
% 0.17/0.37  # Preprocessing time       : 0.027 s
% 0.17/0.37  # Presaturation interreduction done
% 0.17/0.37  
% 0.17/0.37  # Proof found!
% 0.17/0.37  # SZS status Theorem
% 0.17/0.37  # SZS output start CNFRefutation
% 0.17/0.37  fof(t148_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 0.17/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.17/0.37  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.17/0.37  fof(t46_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 0.17/0.37  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.17/0.37  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.17/0.37  fof(t23_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 0.17/0.37  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.17/0.37  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.17/0.37  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4))), inference(assume_negation,[status(cth)],[t148_zfmisc_1])).
% 0.17/0.37  fof(c_0_10, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.17/0.37  fof(c_0_11, plain, ![X11, X12]:r1_tarski(k3_xboole_0(X11,X12),X11), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.17/0.37  fof(c_0_12, plain, ![X28, X29]:(~r2_hidden(X28,X29)|k2_xboole_0(k1_tarski(X28),X29)=X29), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_zfmisc_1])])).
% 0.17/0.37  fof(c_0_13, negated_conjecture, (((r1_tarski(esk1_0,esk2_0)&k3_xboole_0(esk2_0,esk3_0)=k1_tarski(esk4_0))&r2_hidden(esk4_0,esk1_0))&k3_xboole_0(esk1_0,esk3_0)!=k1_tarski(esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.17/0.37  cnf(c_0_14, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.17/0.37  cnf(c_0_15, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.37  fof(c_0_16, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_tarski(X13,X15)|r1_tarski(X13,k3_xboole_0(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.17/0.37  cnf(c_0_17, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.17/0.37  cnf(c_0_18, plain, (k2_xboole_0(k1_tarski(X1),X2)=X2|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.17/0.37  cnf(c_0_19, negated_conjecture, (k3_xboole_0(esk2_0,esk3_0)=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.37  fof(c_0_20, plain, ![X26, X27]:r1_tarski(X26,k2_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.17/0.37  fof(c_0_21, plain, ![X20, X21, X22]:k3_xboole_0(X20,k2_xboole_0(X21,X22))=k2_xboole_0(k3_xboole_0(X20,X21),k3_xboole_0(X20,X22)), inference(variable_rename,[status(thm)],[t23_xboole_1])).
% 0.17/0.37  fof(c_0_22, plain, ![X9, X10]:(~r1_tarski(X9,X10)|k2_xboole_0(X9,X10)=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.17/0.37  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.17/0.37  cnf(c_0_24, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.17/0.37  cnf(c_0_25, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_17])).
% 0.17/0.37  cnf(c_0_26, negated_conjecture, (k2_xboole_0(k3_xboole_0(esk2_0,esk3_0),X1)=X1|~r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.17/0.37  cnf(c_0_27, negated_conjecture, (r2_hidden(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.37  cnf(c_0_28, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.17/0.37  cnf(c_0_29, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.17/0.37  cnf(c_0_30, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.17/0.37  cnf(c_0_31, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.37  cnf(c_0_32, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.17/0.37  cnf(c_0_33, negated_conjecture, (k2_xboole_0(k3_xboole_0(esk2_0,esk3_0),esk1_0)=esk1_0), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.17/0.37  fof(c_0_34, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.17/0.37  cnf(c_0_35, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X1,k2_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.17/0.37  cnf(c_0_36, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)=esk2_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.17/0.37  cnf(c_0_37, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=X1|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_32, c_0_24])).
% 0.17/0.37  cnf(c_0_38, negated_conjecture, (r1_tarski(k3_xboole_0(esk2_0,esk3_0),esk1_0)), inference(spm,[status(thm)],[c_0_28, c_0_33])).
% 0.17/0.37  cnf(c_0_39, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.17/0.37  cnf(c_0_40, negated_conjecture, (r1_tarski(k3_xboole_0(X1,esk1_0),k3_xboole_0(X1,esk2_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.17/0.37  cnf(c_0_41, negated_conjecture, (k3_xboole_0(k3_xboole_0(esk2_0,esk3_0),k3_xboole_0(X1,esk1_0))=k3_xboole_0(esk2_0,esk3_0)|~r1_tarski(k3_xboole_0(esk2_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.17/0.37  cnf(c_0_42, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_15, c_0_39])).
% 0.17/0.37  cnf(c_0_43, negated_conjecture, (r1_tarski(k3_xboole_0(X1,esk1_0),k3_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_40, c_0_39])).
% 0.17/0.37  cnf(c_0_44, negated_conjecture, (k3_xboole_0(esk1_0,esk3_0)!=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.37  cnf(c_0_45, negated_conjecture, (k3_xboole_0(k3_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk2_0,esk3_0))=k3_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_39]), c_0_39])).
% 0.17/0.37  cnf(c_0_46, negated_conjecture, (r1_tarski(k3_xboole_0(esk1_0,X1),k3_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_43, c_0_39])).
% 0.17/0.37  cnf(c_0_47, negated_conjecture, (k3_xboole_0(esk2_0,esk3_0)!=k3_xboole_0(esk1_0,esk3_0)), inference(rw,[status(thm)],[c_0_44, c_0_19])).
% 0.17/0.37  cnf(c_0_48, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_45]), c_0_46])]), c_0_47]), ['proof']).
% 0.17/0.37  # SZS output end CNFRefutation
% 0.17/0.37  # Proof object total steps             : 49
% 0.17/0.37  # Proof object clause steps            : 30
% 0.17/0.37  # Proof object formula steps           : 19
% 0.17/0.37  # Proof object conjectures             : 18
% 0.17/0.37  # Proof object clause conjectures      : 15
% 0.17/0.37  # Proof object formula conjectures     : 3
% 0.17/0.37  # Proof object initial clauses used    : 13
% 0.17/0.37  # Proof object initial formulas used   : 9
% 0.17/0.37  # Proof object generating inferences   : 15
% 0.17/0.37  # Proof object simplifying inferences  : 9
% 0.17/0.37  # Training examples: 0 positive, 0 negative
% 0.17/0.37  # Parsed axioms                        : 12
% 0.17/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.37  # Initial clauses                      : 17
% 0.17/0.37  # Removed in clause preprocessing      : 0
% 0.17/0.37  # Initial clauses in saturation        : 17
% 0.17/0.37  # Processed clauses                    : 168
% 0.17/0.37  # ...of these trivial                  : 30
% 0.17/0.37  # ...subsumed                          : 41
% 0.17/0.37  # ...remaining for further processing  : 97
% 0.17/0.37  # Other redundant clauses eliminated   : 2
% 0.17/0.37  # Clauses deleted for lack of memory   : 0
% 0.17/0.37  # Backward-subsumed                    : 0
% 0.17/0.37  # Backward-rewritten                   : 2
% 0.17/0.37  # Generated clauses                    : 736
% 0.17/0.37  # ...of the previous two non-trivial   : 426
% 0.17/0.37  # Contextual simplify-reflections      : 0
% 0.17/0.37  # Paramodulations                      : 734
% 0.17/0.37  # Factorizations                       : 0
% 0.17/0.37  # Equation resolutions                 : 2
% 0.17/0.37  # Propositional unsat checks           : 0
% 0.17/0.37  #    Propositional check models        : 0
% 0.17/0.37  #    Propositional check unsatisfiable : 0
% 0.17/0.37  #    Propositional clauses             : 0
% 0.17/0.37  #    Propositional clauses after purity: 0
% 0.17/0.37  #    Propositional unsat core size     : 0
% 0.17/0.37  #    Propositional preprocessing time  : 0.000
% 0.17/0.37  #    Propositional encoding time       : 0.000
% 0.17/0.37  #    Propositional solver time         : 0.000
% 0.17/0.37  #    Success case prop preproc time    : 0.000
% 0.17/0.37  #    Success case prop encoding time   : 0.000
% 0.17/0.37  #    Success case prop solver time     : 0.000
% 0.17/0.37  # Current number of processed clauses  : 77
% 0.17/0.37  #    Positive orientable unit clauses  : 46
% 0.17/0.37  #    Positive unorientable unit clauses: 1
% 0.17/0.37  #    Negative unit clauses             : 1
% 0.17/0.37  #    Non-unit-clauses                  : 29
% 0.17/0.37  # Current number of unprocessed clauses: 283
% 0.17/0.37  # ...number of literals in the above   : 357
% 0.17/0.37  # Current number of archived formulas  : 0
% 0.17/0.37  # Current number of archived clauses   : 18
% 0.17/0.37  # Clause-clause subsumption calls (NU) : 171
% 0.17/0.37  # Rec. Clause-clause subsumption calls : 169
% 0.17/0.37  # Non-unit clause-clause subsumptions  : 40
% 0.17/0.37  # Unit Clause-clause subsumption calls : 6
% 0.17/0.37  # Rewrite failures with RHS unbound    : 0
% 0.17/0.37  # BW rewrite match attempts            : 53
% 0.17/0.37  # BW rewrite match successes           : 16
% 0.17/0.37  # Condensation attempts                : 0
% 0.17/0.37  # Condensation successes               : 0
% 0.17/0.37  # Termbank termtop insertions          : 7077
% 0.17/0.37  
% 0.17/0.37  # -------------------------------------------------
% 0.17/0.37  # User time                : 0.036 s
% 0.17/0.37  # System time              : 0.003 s
% 0.17/0.37  # Total time               : 0.039 s
% 0.17/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
