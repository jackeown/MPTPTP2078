%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:07 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 147 expanded)
%              Number of clauses        :   29 (  62 expanded)
%              Number of leaves         :   13 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :  124 ( 293 expanded)
%              Number of equality atoms :   46 ( 135 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k4_xboole_0(X2,X1))
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t39_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( r1_tarski(k3_subset_1(X1,X2),X2)
      <=> X2 = k2_subset_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(t22_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(c_0_13,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,k4_xboole_0(X7,X6))
      | X6 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).

fof(c_0_14,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k5_xboole_0(X4,k3_xboole_0(X4,X5)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_15,plain,(
    ! [X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(X19))
      | k3_subset_1(X19,X20) = k4_xboole_0(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_16,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ( r1_tarski(k3_subset_1(X1,X2),X2)
        <=> X2 = k2_subset_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t39_subset_1])).

cnf(c_0_20,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_17])).

fof(c_0_22,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | k3_subset_1(X24,k3_subset_1(X24,X25)) = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_23,plain,(
    ! [X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | m1_subset_1(k3_subset_1(X21,X22),k1_zfmisc_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_24,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & ( ~ r1_tarski(k3_subset_1(esk2_0,esk3_0),esk3_0)
      | esk3_0 != k2_subset_1(esk2_0) )
    & ( r1_tarski(k3_subset_1(esk2_0,esk3_0),esk3_0)
      | esk3_0 = k2_subset_1(esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_25,plain,(
    ! [X18] : k2_subset_1(X18) = X18 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_26,plain,(
    ! [X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X10,X9)
        | r1_tarski(X10,X8)
        | X9 != k1_zfmisc_1(X8) )
      & ( ~ r1_tarski(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k1_zfmisc_1(X8) )
      & ( ~ r2_hidden(esk1_2(X12,X13),X13)
        | ~ r1_tarski(esk1_2(X12,X13),X12)
        | X13 = k1_zfmisc_1(X12) )
      & ( r2_hidden(esk1_2(X12,X13),X13)
        | r1_tarski(esk1_2(X12,X13),X12)
        | X13 = k1_zfmisc_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_27,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X16,X15)
        | r2_hidden(X16,X15)
        | v1_xboole_0(X15) )
      & ( ~ r2_hidden(X16,X15)
        | m1_subset_1(X16,X15)
        | v1_xboole_0(X15) )
      & ( ~ m1_subset_1(X16,X15)
        | v1_xboole_0(X16)
        | ~ v1_xboole_0(X15) )
      & ( ~ v1_xboole_0(X16)
        | m1_subset_1(X16,X15)
        | ~ v1_xboole_0(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k3_subset_1(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk3_0),esk3_0)
    | esk3_0 = k2_subset_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_33,plain,(
    ! [X26] : k2_subset_1(X26) = k3_subset_1(X26,k1_subset_1(X26)) ),
    inference(variable_rename,[status(thm)],[t22_subset_1])).

fof(c_0_34,plain,(
    ! [X17] : k1_subset_1(X17) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_37,plain,(
    ! [X27] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X27)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_38,plain,(
    ! [X23] : ~ v1_xboole_0(k1_zfmisc_1(X23)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_39,plain,
    ( k3_subset_1(X1,X2) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(k3_subset_1(X1,X2),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( esk3_0 = esk2_0
    | r1_tarski(k3_subset_1(esk2_0,esk3_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_42,plain,
    ( k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X2,X3)
    | X1 != k1_zfmisc_1(X3)
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_45,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk2_0,esk3_0),esk3_0)
    | esk3_0 != k2_subset_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_48,negated_conjecture,
    ( k3_subset_1(esk2_0,esk3_0) = k1_xboole_0
    | esk2_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])])).

cnf(c_0_49,plain,
    ( X1 = k3_subset_1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_32]),c_0_43])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | k1_zfmisc_1(X2) != k1_zfmisc_1(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( esk3_0 != esk2_0
    | ~ r1_tarski(k3_subset_1(esk2_0,esk3_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_32])).

cnf(c_0_52,negated_conjecture,
    ( esk2_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_48]),c_0_49]),c_0_41])])).

cnf(c_0_53,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_49]),c_0_45])])).

cnf(c_0_54,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52]),c_0_52]),c_0_53]),c_0_54])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:23 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.35  # No SInE strategy applied
% 0.19/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___103_C18_F1_PI_AE_Q4_CS_SP_S0Y
% 0.19/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.027 s
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t38_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,k4_xboole_0(X2,X1))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 0.19/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.38  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.19/0.38  fof(t39_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(k3_subset_1(X1,X2),X2)<=>X2=k2_subset_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 0.19/0.38  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.19/0.38  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.19/0.38  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.19/0.38  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.19/0.38  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.19/0.38  fof(t22_subset_1, axiom, ![X1]:k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 0.19/0.38  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 0.19/0.38  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.19/0.38  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.19/0.38  fof(c_0_13, plain, ![X6, X7]:(~r1_tarski(X6,k4_xboole_0(X7,X6))|X6=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).
% 0.19/0.38  fof(c_0_14, plain, ![X4, X5]:k4_xboole_0(X4,X5)=k5_xboole_0(X4,k3_xboole_0(X4,X5)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.38  fof(c_0_15, plain, ![X19, X20]:(~m1_subset_1(X20,k1_zfmisc_1(X19))|k3_subset_1(X19,X20)=k4_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.19/0.38  cnf(c_0_16, plain, (X1=k1_xboole_0|~r1_tarski(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_17, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_18, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  fof(c_0_19, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(k3_subset_1(X1,X2),X2)<=>X2=k2_subset_1(X1)))), inference(assume_negation,[status(cth)],[t39_subset_1])).
% 0.19/0.38  cnf(c_0_20, plain, (X1=k1_xboole_0|~r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.38  cnf(c_0_21, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_18, c_0_17])).
% 0.19/0.38  fof(c_0_22, plain, ![X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(X24))|k3_subset_1(X24,k3_subset_1(X24,X25))=X25), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.19/0.38  fof(c_0_23, plain, ![X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(X21))|m1_subset_1(k3_subset_1(X21,X22),k1_zfmisc_1(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.19/0.38  fof(c_0_24, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&((~r1_tarski(k3_subset_1(esk2_0,esk3_0),esk3_0)|esk3_0!=k2_subset_1(esk2_0))&(r1_tarski(k3_subset_1(esk2_0,esk3_0),esk3_0)|esk3_0=k2_subset_1(esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.19/0.38  fof(c_0_25, plain, ![X18]:k2_subset_1(X18)=X18, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.19/0.38  fof(c_0_26, plain, ![X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X10,X9)|r1_tarski(X10,X8)|X9!=k1_zfmisc_1(X8))&(~r1_tarski(X11,X8)|r2_hidden(X11,X9)|X9!=k1_zfmisc_1(X8)))&((~r2_hidden(esk1_2(X12,X13),X13)|~r1_tarski(esk1_2(X12,X13),X12)|X13=k1_zfmisc_1(X12))&(r2_hidden(esk1_2(X12,X13),X13)|r1_tarski(esk1_2(X12,X13),X12)|X13=k1_zfmisc_1(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.19/0.38  fof(c_0_27, plain, ![X15, X16]:(((~m1_subset_1(X16,X15)|r2_hidden(X16,X15)|v1_xboole_0(X15))&(~r2_hidden(X16,X15)|m1_subset_1(X16,X15)|v1_xboole_0(X15)))&((~m1_subset_1(X16,X15)|v1_xboole_0(X16)|~v1_xboole_0(X15))&(~v1_xboole_0(X16)|m1_subset_1(X16,X15)|~v1_xboole_0(X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.19/0.38  cnf(c_0_28, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,k3_subset_1(X2,X1))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.38  cnf(c_0_29, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  cnf(c_0_30, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk3_0),esk3_0)|esk3_0=k2_subset_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_32, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.38  fof(c_0_33, plain, ![X26]:k2_subset_1(X26)=k3_subset_1(X26,k1_subset_1(X26)), inference(variable_rename,[status(thm)],[t22_subset_1])).
% 0.19/0.38  fof(c_0_34, plain, ![X17]:k1_subset_1(X17)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.19/0.38  cnf(c_0_35, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.38  cnf(c_0_36, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.38  fof(c_0_37, plain, ![X27]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X27)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.19/0.38  fof(c_0_38, plain, ![X23]:~v1_xboole_0(k1_zfmisc_1(X23)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.19/0.38  cnf(c_0_39, plain, (k3_subset_1(X1,X2)=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(k3_subset_1(X1,X2),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (esk3_0=esk2_0|r1_tarski(k3_subset_1(esk2_0,esk3_0),esk3_0)), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_42, plain, (k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.38  cnf(c_0_43, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.38  cnf(c_0_44, plain, (v1_xboole_0(X1)|r1_tarski(X2,X3)|X1!=k1_zfmisc_1(X3)|~m1_subset_1(X2,X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.38  cnf(c_0_45, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.38  cnf(c_0_46, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (~r1_tarski(k3_subset_1(esk2_0,esk3_0),esk3_0)|esk3_0!=k2_subset_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (k3_subset_1(esk2_0,esk3_0)=k1_xboole_0|esk2_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])])).
% 0.19/0.38  cnf(c_0_49, plain, (X1=k3_subset_1(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_32]), c_0_43])).
% 0.19/0.38  cnf(c_0_50, plain, (r1_tarski(k1_xboole_0,X1)|k1_zfmisc_1(X2)!=k1_zfmisc_1(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, (esk3_0!=esk2_0|~r1_tarski(k3_subset_1(esk2_0,esk3_0),esk3_0)), inference(rw,[status(thm)],[c_0_47, c_0_32])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (esk2_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_48]), c_0_49]), c_0_41])])).
% 0.19/0.38  cnf(c_0_53, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_49]), c_0_45])])).
% 0.19/0.38  cnf(c_0_54, plain, (r1_tarski(k1_xboole_0,X1)), inference(er,[status(thm)],[c_0_50])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52]), c_0_52]), c_0_53]), c_0_54])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 56
% 0.19/0.38  # Proof object clause steps            : 29
% 0.19/0.38  # Proof object formula steps           : 27
% 0.19/0.38  # Proof object conjectures             : 11
% 0.19/0.38  # Proof object clause conjectures      : 8
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 15
% 0.19/0.38  # Proof object initial formulas used   : 13
% 0.19/0.38  # Proof object generating inferences   : 8
% 0.19/0.38  # Proof object simplifying inferences  : 20
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 13
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 21
% 0.19/0.38  # Removed in clause preprocessing      : 3
% 0.19/0.38  # Initial clauses in saturation        : 18
% 0.19/0.38  # Processed clauses                    : 63
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 12
% 0.19/0.38  # ...remaining for further processing  : 51
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 15
% 0.19/0.38  # Generated clauses                    : 80
% 0.19/0.38  # ...of the previous two non-trivial   : 73
% 0.19/0.38  # Contextual simplify-reflections      : 1
% 0.19/0.38  # Paramodulations                      : 70
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 10
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 36
% 0.19/0.38  #    Positive orientable unit clauses  : 7
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 1
% 0.19/0.38  #    Non-unit-clauses                  : 28
% 0.19/0.38  # Current number of unprocessed clauses: 20
% 0.19/0.38  # ...number of literals in the above   : 66
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 18
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 238
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 185
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 8
% 0.19/0.38  # Unit Clause-clause subsumption calls : 26
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 10
% 0.19/0.38  # BW rewrite match successes           : 2
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 2209
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.029 s
% 0.19/0.38  # System time              : 0.005 s
% 0.19/0.38  # Total time               : 0.034 s
% 0.19/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
