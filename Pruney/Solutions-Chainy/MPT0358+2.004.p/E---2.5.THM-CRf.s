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
% DateTime   : Thu Dec  3 10:45:50 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 319 expanded)
%              Number of clauses        :   32 ( 135 expanded)
%              Number of leaves         :   15 (  87 expanded)
%              Depth                    :    8
%              Number of atoms          :  105 ( 545 expanded)
%              Number of equality atoms :   49 ( 250 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t22_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t35_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,k3_subset_1(X1,X3))
           => r1_tarski(X3,k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(l97_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(t38_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( r1_tarski(X2,k3_subset_1(X1,X2))
      <=> X2 = k1_subset_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(c_0_15,plain,(
    ! [X15,X16] :
      ( ( ~ r1_xboole_0(X15,X16)
        | k4_xboole_0(X15,X16) = X15 )
      & ( k4_xboole_0(X15,X16) != X15
        | r1_xboole_0(X15,X16) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_16,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_17,plain,(
    ! [X22] : k2_subset_1(X22) = k3_subset_1(X22,k1_subset_1(X22)) ),
    inference(variable_rename,[status(thm)],[t22_subset_1])).

fof(c_0_18,plain,(
    ! [X19] : k2_subset_1(X19) = X19 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_19,plain,(
    ! [X18] : k1_subset_1(X18) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,X13)
      | k3_xboole_0(X12,X13) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_23,plain,(
    ! [X17] : k5_xboole_0(X17,X17) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_24,plain,(
    ! [X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(X20))
      | k3_subset_1(X20,X21) = k4_xboole_0(X20,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_25,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_26,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | ~ m1_subset_1(X25,k1_zfmisc_1(X23))
      | ~ r1_tarski(X24,k3_subset_1(X23,X25))
      | r1_tarski(X25,k3_subset_1(X23,X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_subset_1])])])).

fof(c_0_27,plain,(
    ! [X14] : r1_tarski(k1_xboole_0,X14) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_28,plain,
    ( k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_31,plain,(
    ! [X26] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X26)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_32,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_35,plain,(
    ! [X8,X9] : r1_xboole_0(k3_xboole_0(X8,X9),k5_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[l97_xboole_1])).

cnf(c_0_36,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( r1_tarski(X3,k3_subset_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k3_subset_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( X1 = k3_subset_1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_41,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_42,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ( r1_tarski(X2,k3_subset_1(X1,X2))
        <=> X2 = k1_subset_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t38_subset_1])).

cnf(c_0_43,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_44,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_21])).

cnf(c_0_46,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_37])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41])])).

fof(c_0_48,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
    & ( ~ r1_tarski(esk2_0,k3_subset_1(esk1_0,esk2_0))
      | esk2_0 != k1_subset_1(esk1_0) )
    & ( r1_tarski(esk2_0,k3_subset_1(esk1_0,esk2_0))
      | esk2_0 = k1_subset_1(esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])).

fof(c_0_49,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k5_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,X2) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_53,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk2_0,k3_subset_1(esk1_0,esk2_0))
    | esk2_0 = k1_subset_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k3_subset_1(esk1_0,esk2_0))
    | esk2_0 != k1_subset_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k5_xboole_0(X1,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_33])).

cnf(c_0_57,negated_conjecture,
    ( k5_xboole_0(esk2_0,esk1_0) = k3_subset_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r1_tarski(esk2_0,k3_subset_1(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_54,c_0_30])).

cnf(c_0_60,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ r1_tarski(esk2_0,k3_subset_1(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_55,c_0_30])).

cnf(c_0_61,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])]),c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61]),c_0_61]),c_0_61]),c_0_40]),c_0_39])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.35  % DateTime   : Tue Dec  1 16:38:05 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___103_C18_F1_PI_AE_Q4_CS_SP_S0Y
% 0.12/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.027 s
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.12/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.12/0.38  fof(t22_subset_1, axiom, ![X1]:k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 0.12/0.38  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.12/0.38  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 0.12/0.38  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.12/0.38  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.12/0.38  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.12/0.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.12/0.38  fof(t35_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X3))=>r1_tarski(X3,k3_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 0.12/0.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.12/0.38  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.12/0.38  fof(l97_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 0.12/0.38  fof(t38_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 0.12/0.38  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.12/0.38  fof(c_0_15, plain, ![X15, X16]:((~r1_xboole_0(X15,X16)|k4_xboole_0(X15,X16)=X15)&(k4_xboole_0(X15,X16)!=X15|r1_xboole_0(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.12/0.38  fof(c_0_16, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.12/0.38  fof(c_0_17, plain, ![X22]:k2_subset_1(X22)=k3_subset_1(X22,k1_subset_1(X22)), inference(variable_rename,[status(thm)],[t22_subset_1])).
% 0.12/0.38  fof(c_0_18, plain, ![X19]:k2_subset_1(X19)=X19, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.12/0.38  fof(c_0_19, plain, ![X18]:k1_subset_1(X18)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.12/0.38  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.38  cnf(c_0_21, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  fof(c_0_22, plain, ![X12, X13]:(~r1_tarski(X12,X13)|k3_xboole_0(X12,X13)=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.12/0.38  fof(c_0_23, plain, ![X17]:k5_xboole_0(X17,X17)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.12/0.38  fof(c_0_24, plain, ![X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(X20))|k3_subset_1(X20,X21)=k4_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.12/0.38  fof(c_0_25, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.12/0.38  fof(c_0_26, plain, ![X23, X24, X25]:(~m1_subset_1(X24,k1_zfmisc_1(X23))|(~m1_subset_1(X25,k1_zfmisc_1(X23))|(~r1_tarski(X24,k3_subset_1(X23,X25))|r1_tarski(X25,k3_subset_1(X23,X24))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_subset_1])])])).
% 0.12/0.38  fof(c_0_27, plain, ![X14]:r1_tarski(k1_xboole_0,X14), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.12/0.38  cnf(c_0_28, plain, (k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.38  cnf(c_0_29, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.38  cnf(c_0_30, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.38  fof(c_0_31, plain, ![X26]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X26)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.12/0.38  cnf(c_0_32, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.12/0.38  cnf(c_0_33, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  cnf(c_0_34, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.38  fof(c_0_35, plain, ![X8, X9]:r1_xboole_0(k3_xboole_0(X8,X9),k5_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[l97_xboole_1])).
% 0.12/0.38  cnf(c_0_36, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.38  cnf(c_0_37, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.38  cnf(c_0_38, plain, (r1_tarski(X3,k3_subset_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,k3_subset_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.38  cnf(c_0_39, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.38  cnf(c_0_40, plain, (X1=k3_subset_1(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.12/0.38  cnf(c_0_41, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.38  fof(c_0_42, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1)))), inference(assume_negation,[status(cth)],[t38_subset_1])).
% 0.12/0.38  cnf(c_0_43, plain, (k1_xboole_0=X1|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.12/0.38  cnf(c_0_44, plain, (r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.38  cnf(c_0_45, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_36, c_0_21])).
% 0.12/0.38  cnf(c_0_46, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_33, c_0_37])).
% 0.12/0.38  cnf(c_0_47, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41])])).
% 0.12/0.38  fof(c_0_48, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))&((~r1_tarski(esk2_0,k3_subset_1(esk1_0,esk2_0))|esk2_0!=k1_subset_1(esk1_0))&(r1_tarski(esk2_0,k3_subset_1(esk1_0,esk2_0))|esk2_0=k1_subset_1(esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])).
% 0.12/0.38  fof(c_0_49, plain, ![X6, X7]:k5_xboole_0(X6,X7)=k5_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.12/0.38  cnf(c_0_50, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.12/0.38  cnf(c_0_51, plain, (k5_xboole_0(X1,X2)=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])).
% 0.12/0.38  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.12/0.38  cnf(c_0_53, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.12/0.38  cnf(c_0_54, negated_conjecture, (r1_tarski(esk2_0,k3_subset_1(esk1_0,esk2_0))|esk2_0=k1_subset_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.12/0.38  cnf(c_0_55, negated_conjecture, (~r1_tarski(esk2_0,k3_subset_1(esk1_0,esk2_0))|esk2_0!=k1_subset_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.12/0.38  cnf(c_0_56, plain, (X1=k1_xboole_0|~r1_tarski(X1,k5_xboole_0(X1,X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_50, c_0_33])).
% 0.12/0.38  cnf(c_0_57, negated_conjecture, (k5_xboole_0(esk2_0,esk1_0)=k3_subset_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])).
% 0.12/0.38  cnf(c_0_58, negated_conjecture, (r1_tarski(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_47, c_0_52])).
% 0.12/0.38  cnf(c_0_59, negated_conjecture, (esk2_0=k1_xboole_0|r1_tarski(esk2_0,k3_subset_1(esk1_0,esk2_0))), inference(rw,[status(thm)],[c_0_54, c_0_30])).
% 0.12/0.38  cnf(c_0_60, negated_conjecture, (esk2_0!=k1_xboole_0|~r1_tarski(esk2_0,k3_subset_1(esk1_0,esk2_0))), inference(rw,[status(thm)],[c_0_55, c_0_30])).
% 0.12/0.38  cnf(c_0_61, negated_conjecture, (esk2_0=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])]), c_0_59])).
% 0.12/0.38  cnf(c_0_62, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61]), c_0_61]), c_0_61]), c_0_40]), c_0_39])]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 63
% 0.12/0.38  # Proof object clause steps            : 32
% 0.12/0.38  # Proof object formula steps           : 31
% 0.12/0.38  # Proof object conjectures             : 12
% 0.12/0.38  # Proof object clause conjectures      : 9
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 17
% 0.12/0.38  # Proof object initial formulas used   : 15
% 0.12/0.38  # Proof object generating inferences   : 9
% 0.12/0.38  # Proof object simplifying inferences  : 21
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 15
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 18
% 0.12/0.38  # Removed in clause preprocessing      : 3
% 0.12/0.38  # Initial clauses in saturation        : 15
% 0.12/0.38  # Processed clauses                    : 109
% 0.12/0.38  # ...of these trivial                  : 12
% 0.12/0.38  # ...subsumed                          : 37
% 0.12/0.38  # ...remaining for further processing  : 60
% 0.12/0.38  # Other redundant clauses eliminated   : 0
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 1
% 0.12/0.38  # Backward-rewritten                   : 18
% 0.12/0.38  # Generated clauses                    : 232
% 0.12/0.38  # ...of the previous two non-trivial   : 184
% 0.12/0.38  # Contextual simplify-reflections      : 7
% 0.12/0.38  # Paramodulations                      : 232
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 0
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 41
% 0.12/0.38  #    Positive orientable unit clauses  : 13
% 0.12/0.38  #    Positive unorientable unit clauses: 2
% 0.12/0.38  #    Negative unit clauses             : 0
% 0.12/0.38  #    Non-unit-clauses                  : 26
% 0.12/0.38  # Current number of unprocessed clauses: 83
% 0.12/0.38  # ...number of literals in the above   : 241
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 22
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 198
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 181
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 45
% 0.12/0.38  # Unit Clause-clause subsumption calls : 3
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 9
% 0.12/0.38  # BW rewrite match successes           : 8
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 2755
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.031 s
% 0.12/0.38  # System time              : 0.004 s
% 0.12/0.38  # Total time               : 0.035 s
% 0.12/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
