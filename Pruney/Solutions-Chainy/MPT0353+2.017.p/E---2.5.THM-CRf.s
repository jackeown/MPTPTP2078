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
% DateTime   : Thu Dec  3 10:45:44 EST 2020

% Result     : Theorem 0.52s
% Output     : CNFRefutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 128 expanded)
%              Number of clauses        :   32 (  55 expanded)
%              Number of leaves         :   10 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 ( 213 expanded)
%              Number of equality atoms :   43 ( 109 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t32_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(t111_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k4_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t32_subset_1])).

fof(c_0_11,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | m1_subset_1(k3_subset_1(X15,X16),k1_zfmisc_1(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_12,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
    & k7_subset_1(esk1_0,esk2_0,esk3_0) != k9_subset_1(esk1_0,esk2_0,k3_subset_1(esk1_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_13,plain,(
    ! [X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | k3_subset_1(X13,X14) = k4_xboole_0(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_14,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | k3_subset_1(X17,k3_subset_1(X17,X18)) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_15,plain,(
    ! [X6,X7,X8] : k4_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X8,X7)) = k3_xboole_0(k4_xboole_0(X6,X8),X7) ),
    inference(variable_rename,[status(thm)],[t111_xboole_1])).

fof(c_0_16,plain,(
    ! [X11,X12] : k4_xboole_0(X11,k4_xboole_0(X11,X12)) = k3_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_17,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_18,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_23,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(X19))
      | k7_subset_1(X19,X20,X21) = k4_xboole_0(X20,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_24,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(X22))
      | k9_subset_1(X22,X23,X24) = k3_xboole_0(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_25,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k4_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( k3_subset_1(esk1_0,esk2_0) = k4_xboole_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_19])).

fof(c_0_31,plain,(
    ! [X9,X10] : k4_xboole_0(X9,k3_xboole_0(X9,X10)) = k4_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_32,negated_conjecture,
    ( k7_subset_1(esk1_0,esk2_0,esk3_0) != k9_subset_1(esk1_0,esk2_0,k3_subset_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_33,negated_conjecture,
    ( k3_subset_1(esk1_0,esk3_0) = k4_xboole_0(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_22])).

cnf(c_0_34,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk1_0,esk3_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_22])).

cnf(c_0_37,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X2))) = k4_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(k4_xboole_0(X1,X3),X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_26]),c_0_26])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(esk1_0,esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( k3_subset_1(esk1_0,k4_xboole_0(esk1_0,esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( k9_subset_1(esk1_0,esk2_0,k4_xboole_0(esk1_0,esk3_0)) != k7_subset_1(esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( k7_subset_1(esk1_0,esk2_0,X1) = k4_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_19])).

cnf(c_0_44,plain,
    ( k9_subset_1(X2,X3,X1) = k4_xboole_0(X3,k4_xboole_0(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_26])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(esk1_0,esk3_0),k1_zfmisc_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_33])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(k4_xboole_0(X1,X3),X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_39]),c_0_40])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_41,c_0_26])).

cnf(c_0_49,negated_conjecture,
    ( k9_subset_1(esk1_0,esk2_0,k4_xboole_0(esk1_0,esk3_0)) != k4_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( k9_subset_1(esk1_0,X1,k4_xboole_0(esk1_0,esk3_0)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(esk1_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk1_0,X1))) = k4_xboole_0(esk2_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_38])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50]),c_0_51])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:31:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.52/0.68  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S081N
% 0.52/0.68  # and selection function SelectCQArNTNp.
% 0.52/0.68  #
% 0.52/0.68  # Preprocessing time       : 0.026 s
% 0.52/0.68  # Presaturation interreduction done
% 0.52/0.68  
% 0.52/0.68  # Proof found!
% 0.52/0.68  # SZS status Theorem
% 0.52/0.68  # SZS output start CNFRefutation
% 0.52/0.68  fof(t32_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_subset_1)).
% 0.52/0.68  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.52/0.68  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.52/0.68  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.52/0.68  fof(t111_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k4_xboole_0(X1,X3),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_xboole_1)).
% 0.52/0.68  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.52/0.68  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.52/0.68  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.52/0.68  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.52/0.68  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.52/0.68  fof(c_0_10, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3))))), inference(assume_negation,[status(cth)],[t32_subset_1])).
% 0.52/0.68  fof(c_0_11, plain, ![X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(X15))|m1_subset_1(k3_subset_1(X15,X16),k1_zfmisc_1(X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.52/0.68  fof(c_0_12, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))&k7_subset_1(esk1_0,esk2_0,esk3_0)!=k9_subset_1(esk1_0,esk2_0,k3_subset_1(esk1_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.52/0.68  fof(c_0_13, plain, ![X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(X13))|k3_subset_1(X13,X14)=k4_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.52/0.68  fof(c_0_14, plain, ![X17, X18]:(~m1_subset_1(X18,k1_zfmisc_1(X17))|k3_subset_1(X17,k3_subset_1(X17,X18))=X18), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.52/0.68  fof(c_0_15, plain, ![X6, X7, X8]:k4_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X8,X7))=k3_xboole_0(k4_xboole_0(X6,X8),X7), inference(variable_rename,[status(thm)],[t111_xboole_1])).
% 0.52/0.68  fof(c_0_16, plain, ![X11, X12]:k4_xboole_0(X11,k4_xboole_0(X11,X12))=k3_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.52/0.68  fof(c_0_17, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.52/0.68  cnf(c_0_18, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.52/0.68  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.52/0.68  cnf(c_0_20, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.52/0.68  cnf(c_0_21, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.52/0.68  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.52/0.68  fof(c_0_23, plain, ![X19, X20, X21]:(~m1_subset_1(X20,k1_zfmisc_1(X19))|k7_subset_1(X19,X20,X21)=k4_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.52/0.68  fof(c_0_24, plain, ![X22, X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(X22))|k9_subset_1(X22,X23,X24)=k3_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.52/0.68  cnf(c_0_25, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k4_xboole_0(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.52/0.68  cnf(c_0_26, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.52/0.68  cnf(c_0_27, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.52/0.68  cnf(c_0_28, negated_conjecture, (m1_subset_1(k3_subset_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.52/0.68  cnf(c_0_29, negated_conjecture, (k3_subset_1(esk1_0,esk2_0)=k4_xboole_0(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_20, c_0_19])).
% 0.52/0.68  cnf(c_0_30, negated_conjecture, (k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk2_0))=esk2_0), inference(spm,[status(thm)],[c_0_21, c_0_19])).
% 0.52/0.68  fof(c_0_31, plain, ![X9, X10]:k4_xboole_0(X9,k3_xboole_0(X9,X10))=k4_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.52/0.68  cnf(c_0_32, negated_conjecture, (k7_subset_1(esk1_0,esk2_0,esk3_0)!=k9_subset_1(esk1_0,esk2_0,k3_subset_1(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.52/0.68  cnf(c_0_33, negated_conjecture, (k3_subset_1(esk1_0,esk3_0)=k4_xboole_0(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_22])).
% 0.52/0.68  cnf(c_0_34, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.52/0.68  cnf(c_0_35, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.52/0.68  cnf(c_0_36, negated_conjecture, (m1_subset_1(k3_subset_1(esk1_0,esk3_0),k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_18, c_0_22])).
% 0.52/0.68  cnf(c_0_37, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X2)))=k4_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(k4_xboole_0(X1,X3),X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_26]), c_0_26])).
% 0.52/0.68  cnf(c_0_38, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_26]), c_0_26])).
% 0.52/0.68  cnf(c_0_39, negated_conjecture, (m1_subset_1(k4_xboole_0(esk1_0,esk2_0),k1_zfmisc_1(esk1_0))), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.52/0.68  cnf(c_0_40, negated_conjecture, (k3_subset_1(esk1_0,k4_xboole_0(esk1_0,esk2_0))=esk2_0), inference(rw,[status(thm)],[c_0_30, c_0_29])).
% 0.52/0.68  cnf(c_0_41, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.52/0.68  cnf(c_0_42, negated_conjecture, (k9_subset_1(esk1_0,esk2_0,k4_xboole_0(esk1_0,esk3_0))!=k7_subset_1(esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.52/0.68  cnf(c_0_43, negated_conjecture, (k7_subset_1(esk1_0,esk2_0,X1)=k4_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_34, c_0_19])).
% 0.52/0.68  cnf(c_0_44, plain, (k9_subset_1(X2,X3,X1)=k4_xboole_0(X3,k4_xboole_0(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_35, c_0_26])).
% 0.52/0.68  cnf(c_0_45, negated_conjecture, (m1_subset_1(k4_xboole_0(esk1_0,esk3_0),k1_zfmisc_1(esk1_0))), inference(rw,[status(thm)],[c_0_36, c_0_33])).
% 0.52/0.68  cnf(c_0_46, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X2,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(k4_xboole_0(X1,X3),X2))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.52/0.68  cnf(c_0_47, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_39]), c_0_40])).
% 0.52/0.68  cnf(c_0_48, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_41, c_0_26])).
% 0.52/0.68  cnf(c_0_49, negated_conjecture, (k9_subset_1(esk1_0,esk2_0,k4_xboole_0(esk1_0,esk3_0))!=k4_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.52/0.68  cnf(c_0_50, negated_conjecture, (k9_subset_1(esk1_0,X1,k4_xboole_0(esk1_0,esk3_0))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(esk1_0,esk3_0)))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.52/0.68  cnf(c_0_51, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk1_0,X1)))=k4_xboole_0(esk2_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_38])).
% 0.52/0.68  cnf(c_0_52, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50]), c_0_51])]), ['proof']).
% 0.52/0.68  # SZS output end CNFRefutation
% 0.52/0.68  # Proof object total steps             : 53
% 0.52/0.68  # Proof object clause steps            : 32
% 0.52/0.68  # Proof object formula steps           : 21
% 0.52/0.68  # Proof object conjectures             : 21
% 0.52/0.68  # Proof object clause conjectures      : 18
% 0.52/0.68  # Proof object formula conjectures     : 3
% 0.52/0.68  # Proof object initial clauses used    : 12
% 0.52/0.68  # Proof object initial formulas used   : 10
% 0.52/0.68  # Proof object generating inferences   : 10
% 0.52/0.68  # Proof object simplifying inferences  : 18
% 0.52/0.68  # Training examples: 0 positive, 0 negative
% 0.52/0.68  # Parsed axioms                        : 10
% 0.52/0.68  # Removed by relevancy pruning/SinE    : 0
% 0.52/0.68  # Initial clauses                      : 12
% 0.52/0.68  # Removed in clause preprocessing      : 1
% 0.52/0.68  # Initial clauses in saturation        : 11
% 0.52/0.68  # Processed clauses                    : 523
% 0.52/0.68  # ...of these trivial                  : 168
% 0.52/0.68  # ...subsumed                          : 75
% 0.52/0.68  # ...remaining for further processing  : 280
% 0.52/0.68  # Other redundant clauses eliminated   : 0
% 0.52/0.68  # Clauses deleted for lack of memory   : 0
% 0.52/0.68  # Backward-subsumed                    : 4
% 0.52/0.68  # Backward-rewritten                   : 144
% 0.52/0.68  # Generated clauses                    : 19189
% 0.52/0.68  # ...of the previous two non-trivial   : 14294
% 0.52/0.68  # Contextual simplify-reflections      : 0
% 0.52/0.68  # Paramodulations                      : 19189
% 0.52/0.68  # Factorizations                       : 0
% 0.52/0.68  # Equation resolutions                 : 0
% 0.52/0.68  # Propositional unsat checks           : 0
% 0.52/0.68  #    Propositional check models        : 0
% 0.52/0.68  #    Propositional check unsatisfiable : 0
% 0.52/0.68  #    Propositional clauses             : 0
% 0.52/0.68  #    Propositional clauses after purity: 0
% 0.52/0.68  #    Propositional unsat core size     : 0
% 0.52/0.68  #    Propositional preprocessing time  : 0.000
% 0.52/0.68  #    Propositional encoding time       : 0.000
% 0.52/0.68  #    Propositional solver time         : 0.000
% 0.52/0.68  #    Success case prop preproc time    : 0.000
% 0.52/0.68  #    Success case prop encoding time   : 0.000
% 0.52/0.68  #    Success case prop solver time     : 0.000
% 0.52/0.68  # Current number of processed clauses  : 121
% 0.52/0.68  #    Positive orientable unit clauses  : 104
% 0.52/0.68  #    Positive unorientable unit clauses: 12
% 0.52/0.68  #    Negative unit clauses             : 0
% 0.52/0.68  #    Non-unit-clauses                  : 5
% 0.52/0.68  # Current number of unprocessed clauses: 13578
% 0.52/0.68  # ...number of literals in the above   : 13578
% 0.52/0.68  # Current number of archived formulas  : 0
% 0.52/0.68  # Current number of archived clauses   : 160
% 0.52/0.68  # Clause-clause subsumption calls (NU) : 2
% 0.52/0.68  # Rec. Clause-clause subsumption calls : 2
% 0.52/0.68  # Non-unit clause-clause subsumptions  : 0
% 0.52/0.68  # Unit Clause-clause subsumption calls : 517
% 0.52/0.68  # Rewrite failures with RHS unbound    : 0
% 0.52/0.68  # BW rewrite match attempts            : 2222
% 0.52/0.68  # BW rewrite match successes           : 462
% 0.52/0.68  # Condensation attempts                : 0
% 0.52/0.68  # Condensation successes               : 0
% 0.52/0.68  # Termbank termtop insertions          : 456075
% 0.52/0.68  
% 0.52/0.68  # -------------------------------------------------
% 0.52/0.68  # User time                : 0.330 s
% 0.52/0.68  # System time              : 0.016 s
% 0.52/0.68  # Total time               : 0.346 s
% 0.52/0.68  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
