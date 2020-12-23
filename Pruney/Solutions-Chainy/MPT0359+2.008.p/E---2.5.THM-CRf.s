%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:00 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 274 expanded)
%              Number of clauses        :   35 ( 113 expanded)
%              Number of leaves         :   12 (  71 expanded)
%              Depth                    :   11
%              Number of atoms          :  105 ( 530 expanded)
%              Number of equality atoms :   49 ( 255 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t39_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( r1_tarski(k3_subset_1(X1,X2),X2)
      <=> X2 = k2_subset_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(t38_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k4_xboole_0(X2,X1))
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t109_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ( r1_tarski(k3_subset_1(X1,X2),X2)
        <=> X2 = k2_subset_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t39_subset_1])).

fof(c_0_13,plain,(
    ! [X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(X28))
      | k3_subset_1(X28,X29) = k4_xboole_0(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_14,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
    & ( ~ r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)
      | esk2_0 != k2_subset_1(esk1_0) )
    & ( r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)
      | esk2_0 = k2_subset_1(esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_15,plain,(
    ! [X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(X30))
      | m1_subset_1(k3_subset_1(X30,X31),k1_zfmisc_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_16,plain,(
    ! [X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(X32))
      | k3_subset_1(X32,k3_subset_1(X32,X33)) = X33 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_17,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_20,plain,(
    ! [X20,X21] : k4_xboole_0(X20,k4_xboole_0(X20,X21)) = k3_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_21,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( k3_subset_1(esk1_0,esk2_0) = k4_xboole_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X27] : k2_subset_1(X27) = X27 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_27,plain,(
    ! [X16,X17] :
      ( ~ r1_tarski(X16,k4_xboole_0(X17,X16))
      | X16 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).

cnf(c_0_28,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X2)) = k4_xboole_0(X1,k3_subset_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( k3_subset_1(esk1_0,k4_xboole_0(esk1_0,esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_18]),c_0_23])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_25])).

fof(c_0_31,plain,(
    ! [X14,X15] : r1_tarski(k4_xboole_0(X14,X15),X14) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_32,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)
    | esk2_0 != k2_subset_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_18]),c_0_23]),c_0_29]),c_0_23]),c_0_30])).

cnf(c_0_36,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_37,plain,(
    ! [X18] : k4_xboole_0(X18,k1_xboole_0) = X18 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)
    | esk2_0 = k2_subset_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_39,negated_conjecture,
    ( esk2_0 != esk1_0
    | ~ r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_40,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,X11)
      | r1_tarski(k4_xboole_0(X10,X12),X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_xboole_1])])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk1_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( esk2_0 = esk1_0
    | r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_38,c_0_33])).

fof(c_0_45,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_46,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_30])).

cnf(c_0_47,negated_conjecture,
    ( esk1_0 != esk2_0
    | ~ r1_tarski(k4_xboole_0(esk1_0,esk2_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_39,c_0_23])).

cnf(c_0_48,plain,
    ( r1_tarski(k4_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) = k1_xboole_0
    | ~ r1_tarski(k4_xboole_0(esk1_0,esk2_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( esk1_0 = esk2_0
    | r1_tarski(k4_xboole_0(esk1_0,esk2_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_44,c_0_23])).

cnf(c_0_51,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_35])).

cnf(c_0_53,negated_conjecture,
    ( esk1_0 != esk2_0
    | ~ r1_tarski(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) = k1_xboole_0
    | esk1_0 = esk2_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( esk1_0 = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_54]),c_0_43]),c_0_42]),c_0_43])])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57]),c_0_58])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___103_C18_F1_PI_AE_Q4_CS_SP_S0Y
% 0.13/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t39_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(k3_subset_1(X1,X2),X2)<=>X2=k2_subset_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 0.13/0.37  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.13/0.37  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.13/0.37  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.13/0.37  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.13/0.37  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.13/0.37  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.13/0.37  fof(t38_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,k4_xboole_0(X2,X1))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 0.13/0.37  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.13/0.37  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.13/0.37  fof(t109_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 0.13/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.37  fof(c_0_12, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(k3_subset_1(X1,X2),X2)<=>X2=k2_subset_1(X1)))), inference(assume_negation,[status(cth)],[t39_subset_1])).
% 0.13/0.37  fof(c_0_13, plain, ![X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(X28))|k3_subset_1(X28,X29)=k4_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.13/0.37  fof(c_0_14, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))&((~r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)|esk2_0!=k2_subset_1(esk1_0))&(r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)|esk2_0=k2_subset_1(esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.13/0.37  fof(c_0_15, plain, ![X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(X30))|m1_subset_1(k3_subset_1(X30,X31),k1_zfmisc_1(X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.13/0.37  fof(c_0_16, plain, ![X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(X32))|k3_subset_1(X32,k3_subset_1(X32,X33))=X33), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.13/0.37  cnf(c_0_17, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  fof(c_0_19, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.13/0.37  fof(c_0_20, plain, ![X20, X21]:k4_xboole_0(X20,k4_xboole_0(X20,X21))=k3_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.13/0.37  cnf(c_0_21, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_22, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, (k3_subset_1(esk1_0,esk2_0)=k4_xboole_0(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.37  cnf(c_0_24, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  cnf(c_0_25, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.37  fof(c_0_26, plain, ![X27]:k2_subset_1(X27)=X27, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.13/0.37  fof(c_0_27, plain, ![X16, X17]:(~r1_tarski(X16,k4_xboole_0(X17,X16))|X16=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).
% 0.13/0.37  cnf(c_0_28, plain, (k3_subset_1(X1,k3_subset_1(X1,X2))=k4_xboole_0(X1,k3_subset_1(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_17, c_0_21])).
% 0.13/0.37  cnf(c_0_29, negated_conjecture, (k3_subset_1(esk1_0,k4_xboole_0(esk1_0,esk2_0))=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_18]), c_0_23])).
% 0.13/0.37  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_25])).
% 0.13/0.37  fof(c_0_31, plain, ![X14, X15]:r1_tarski(k4_xboole_0(X14,X15),X14), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.13/0.37  cnf(c_0_32, negated_conjecture, (~r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)|esk2_0!=k2_subset_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_33, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.37  cnf(c_0_34, plain, (X1=k1_xboole_0|~r1_tarski(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.37  cnf(c_0_35, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0))=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_18]), c_0_23]), c_0_29]), c_0_23]), c_0_30])).
% 0.13/0.37  cnf(c_0_36, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.37  fof(c_0_37, plain, ![X18]:k4_xboole_0(X18,k1_xboole_0)=X18, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.13/0.37  cnf(c_0_38, negated_conjecture, (r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)|esk2_0=k2_subset_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_39, negated_conjecture, (esk2_0!=esk1_0|~r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.37  fof(c_0_40, plain, ![X10, X11, X12]:(~r1_tarski(X10,X11)|r1_tarski(k4_xboole_0(X10,X12),X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_xboole_1])])).
% 0.13/0.37  cnf(c_0_41, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_34, c_0_30])).
% 0.13/0.37  cnf(c_0_42, negated_conjecture, (k4_xboole_0(esk2_0,esk1_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 0.13/0.37  cnf(c_0_43, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.37  cnf(c_0_44, negated_conjecture, (esk2_0=esk1_0|r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)), inference(rw,[status(thm)],[c_0_38, c_0_33])).
% 0.13/0.37  fof(c_0_45, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.37  cnf(c_0_46, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_36, c_0_30])).
% 0.13/0.37  cnf(c_0_47, negated_conjecture, (esk1_0!=esk2_0|~r1_tarski(k4_xboole_0(esk1_0,esk2_0),esk2_0)), inference(rw,[status(thm)],[c_0_39, c_0_23])).
% 0.13/0.37  cnf(c_0_48, plain, (r1_tarski(k4_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.37  cnf(c_0_49, negated_conjecture, (k4_xboole_0(esk1_0,esk2_0)=k1_xboole_0|~r1_tarski(k4_xboole_0(esk1_0,esk2_0),esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.13/0.37  cnf(c_0_50, negated_conjecture, (esk1_0=esk2_0|r1_tarski(k4_xboole_0(esk1_0,esk2_0),esk2_0)), inference(rw,[status(thm)],[c_0_44, c_0_23])).
% 0.13/0.37  cnf(c_0_51, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.37  cnf(c_0_52, negated_conjecture, (r1_tarski(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_46, c_0_35])).
% 0.13/0.37  cnf(c_0_53, negated_conjecture, (esk1_0!=esk2_0|~r1_tarski(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.13/0.37  cnf(c_0_54, negated_conjecture, (k4_xboole_0(esk1_0,esk2_0)=k1_xboole_0|esk1_0=esk2_0), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.13/0.37  cnf(c_0_55, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.37  cnf(c_0_56, negated_conjecture, (~r1_tarski(esk1_0,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])).
% 0.13/0.37  cnf(c_0_57, negated_conjecture, (esk1_0=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_54]), c_0_43]), c_0_42]), c_0_43])])).
% 0.13/0.37  cnf(c_0_58, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_55])).
% 0.13/0.37  cnf(c_0_59, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57]), c_0_58])]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 60
% 0.13/0.37  # Proof object clause steps            : 35
% 0.13/0.37  # Proof object formula steps           : 25
% 0.13/0.37  # Proof object conjectures             : 21
% 0.13/0.37  # Proof object clause conjectures      : 18
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 15
% 0.13/0.37  # Proof object initial formulas used   : 12
% 0.13/0.37  # Proof object generating inferences   : 13
% 0.13/0.37  # Proof object simplifying inferences  : 23
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 19
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 24
% 0.13/0.37  # Removed in clause preprocessing      : 4
% 0.13/0.37  # Initial clauses in saturation        : 20
% 0.13/0.37  # Processed clauses                    : 118
% 0.13/0.37  # ...of these trivial                  : 17
% 0.13/0.37  # ...subsumed                          : 38
% 0.13/0.37  # ...remaining for further processing  : 63
% 0.13/0.37  # Other redundant clauses eliminated   : 2
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 2
% 0.13/0.37  # Backward-rewritten                   : 25
% 0.13/0.37  # Generated clauses                    : 298
% 0.13/0.37  # ...of the previous two non-trivial   : 223
% 0.13/0.37  # Contextual simplify-reflections      : 3
% 0.13/0.37  # Paramodulations                      : 296
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 2
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
% 0.13/0.37  # Current number of processed clauses  : 34
% 0.13/0.37  #    Positive orientable unit clauses  : 11
% 0.13/0.37  #    Positive unorientable unit clauses: 2
% 0.13/0.37  #    Negative unit clauses             : 0
% 0.13/0.37  #    Non-unit-clauses                  : 21
% 0.13/0.37  # Current number of unprocessed clauses: 113
% 0.13/0.37  # ...number of literals in the above   : 259
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 31
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 201
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 165
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 40
% 0.13/0.37  # Unit Clause-clause subsumption calls : 18
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 25
% 0.13/0.37  # BW rewrite match successes           : 8
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 3845
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.031 s
% 0.13/0.37  # System time              : 0.005 s
% 0.13/0.37  # Total time               : 0.036 s
% 0.13/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
