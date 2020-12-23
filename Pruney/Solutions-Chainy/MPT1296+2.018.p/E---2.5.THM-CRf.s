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
% DateTime   : Thu Dec  3 11:12:59 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   31 (  53 expanded)
%              Number of clauses        :   16 (  21 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :   67 ( 122 expanded)
%              Number of equality atoms :   35 (  65 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_tops_2,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( X2 != k1_xboole_0
       => k5_setfam_1(X1,k7_setfam_1(X1,X2)) = k3_subset_1(X1,k6_setfam_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tops_2)).

fof(dt_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(dt_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(involutiveness_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k7_setfam_1(X1,k7_setfam_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(t11_tops_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( X2 != k1_xboole_0
       => k6_setfam_1(X1,k7_setfam_1(X1,X2)) = k3_subset_1(X1,k5_setfam_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tops_2)).

fof(t10_tops_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( ~ ( X2 != k1_xboole_0
            & k7_setfam_1(X1,X2) = k1_xboole_0 )
        & ~ ( k7_setfam_1(X1,X2) != k1_xboole_0
            & X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tops_2)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ( X2 != k1_xboole_0
         => k5_setfam_1(X1,k7_setfam_1(X1,X2)) = k3_subset_1(X1,k6_setfam_1(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t12_tops_2])).

fof(c_0_8,plain,(
    ! [X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(X7)))
      | m1_subset_1(k7_setfam_1(X7,X8),k1_zfmisc_1(k1_zfmisc_1(X7))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

fof(c_0_9,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    & esk2_0 != k1_xboole_0
    & k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)) != k3_subset_1(esk1_0,k6_setfam_1(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X5,X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X5)))
      | m1_subset_1(k5_setfam_1(X5,X6),k1_zfmisc_1(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).

cnf(c_0_11,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X9,X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9)))
      | k7_setfam_1(X9,k7_setfam_1(X9,X10)) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).

fof(c_0_14,plain,(
    ! [X3,X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | k3_subset_1(X3,k3_subset_1(X3,X4)) = X4 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_15,plain,
    ( m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(k7_setfam_1(esk1_0,esk2_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_17,plain,(
    ! [X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13)))
      | X14 = k1_xboole_0
      | k6_setfam_1(X13,k7_setfam_1(X13,X14)) = k3_subset_1(X13,k5_setfam_1(X13,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tops_2])])).

cnf(c_0_18,plain,
    ( k7_setfam_1(X2,k7_setfam_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | k6_setfam_1(X2,k7_setfam_1(X2,X1)) = k3_subset_1(X2,k5_setfam_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( k7_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_12])).

fof(c_0_23,plain,(
    ! [X11,X12] :
      ( ( X12 = k1_xboole_0
        | k7_setfam_1(X11,X12) != k1_xboole_0
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X11))) )
      & ( k7_setfam_1(X11,X12) = k1_xboole_0
        | X12 != k1_xboole_0
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X11))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_tops_2])])])).

cnf(c_0_24,negated_conjecture,
    ( k3_subset_1(esk1_0,k3_subset_1(esk1_0,k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)))) = k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( k3_subset_1(esk1_0,k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))) = k6_setfam_1(esk1_0,esk2_0)
    | k7_setfam_1(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_16]),c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)) != k3_subset_1(esk1_0,k6_setfam_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,plain,
    ( X1 = k1_xboole_0
    | k7_setfam_1(X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( k7_setfam_1(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_12])]),c_0_29]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:32:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00DA
% 0.13/0.37  # and selection function SelectSmallestOrientable.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.026 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t12_tops_2, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X2!=k1_xboole_0=>k5_setfam_1(X1,k7_setfam_1(X1,X2))=k3_subset_1(X1,k6_setfam_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tops_2)).
% 0.13/0.37  fof(dt_k7_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 0.13/0.37  fof(dt_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 0.13/0.37  fof(involutiveness_k7_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k7_setfam_1(X1,k7_setfam_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 0.13/0.37  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.13/0.37  fof(t11_tops_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X2!=k1_xboole_0=>k6_setfam_1(X1,k7_setfam_1(X1,X2))=k3_subset_1(X1,k5_setfam_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tops_2)).
% 0.13/0.37  fof(t10_tops_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(~((X2!=k1_xboole_0&k7_setfam_1(X1,X2)=k1_xboole_0))&~((k7_setfam_1(X1,X2)!=k1_xboole_0&X2=k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_tops_2)).
% 0.13/0.37  fof(c_0_7, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X2!=k1_xboole_0=>k5_setfam_1(X1,k7_setfam_1(X1,X2))=k3_subset_1(X1,k6_setfam_1(X1,X2))))), inference(assume_negation,[status(cth)],[t12_tops_2])).
% 0.13/0.37  fof(c_0_8, plain, ![X7, X8]:(~m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(X7)))|m1_subset_1(k7_setfam_1(X7,X8),k1_zfmisc_1(k1_zfmisc_1(X7)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).
% 0.13/0.37  fof(c_0_9, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))&(esk2_0!=k1_xboole_0&k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))!=k3_subset_1(esk1_0,k6_setfam_1(esk1_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.13/0.37  fof(c_0_10, plain, ![X5, X6]:(~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X5)))|m1_subset_1(k5_setfam_1(X5,X6),k1_zfmisc_1(X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).
% 0.13/0.37  cnf(c_0_11, plain, (m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  fof(c_0_13, plain, ![X9, X10]:(~m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9)))|k7_setfam_1(X9,k7_setfam_1(X9,X10))=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).
% 0.13/0.37  fof(c_0_14, plain, ![X3, X4]:(~m1_subset_1(X4,k1_zfmisc_1(X3))|k3_subset_1(X3,k3_subset_1(X3,X4))=X4), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.13/0.37  cnf(c_0_15, plain, (m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_16, negated_conjecture, (m1_subset_1(k7_setfam_1(esk1_0,esk2_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.13/0.37  fof(c_0_17, plain, ![X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13)))|(X14=k1_xboole_0|k6_setfam_1(X13,k7_setfam_1(X13,X14))=k3_subset_1(X13,k5_setfam_1(X13,X14)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tops_2])])).
% 0.13/0.37  cnf(c_0_18, plain, (k7_setfam_1(X2,k7_setfam_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_19, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_20, negated_conjecture, (m1_subset_1(k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)),k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.37  cnf(c_0_21, plain, (X1=k1_xboole_0|k6_setfam_1(X2,k7_setfam_1(X2,X1))=k3_subset_1(X2,k5_setfam_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (k7_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))=esk2_0), inference(spm,[status(thm)],[c_0_18, c_0_12])).
% 0.13/0.37  fof(c_0_23, plain, ![X11, X12]:((X12=k1_xboole_0|k7_setfam_1(X11,X12)!=k1_xboole_0|~m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X11))))&(k7_setfam_1(X11,X12)=k1_xboole_0|X12!=k1_xboole_0|~m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X11))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_tops_2])])])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (k3_subset_1(esk1_0,k3_subset_1(esk1_0,k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))))=k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (k3_subset_1(esk1_0,k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)))=k6_setfam_1(esk1_0,esk2_0)|k7_setfam_1(esk1_0,esk2_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_16]), c_0_22])).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, (k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))!=k3_subset_1(esk1_0,k6_setfam_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_27, plain, (X1=k1_xboole_0|k7_setfam_1(X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (k7_setfam_1(esk1_0,esk2_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.13/0.37  cnf(c_0_29, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_12])]), c_0_29]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 31
% 0.13/0.37  # Proof object clause steps            : 16
% 0.13/0.37  # Proof object formula steps           : 15
% 0.13/0.37  # Proof object conjectures             : 13
% 0.13/0.37  # Proof object clause conjectures      : 10
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 9
% 0.13/0.37  # Proof object initial formulas used   : 7
% 0.13/0.37  # Proof object generating inferences   : 7
% 0.13/0.37  # Proof object simplifying inferences  : 5
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 7
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 10
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 10
% 0.13/0.37  # Processed clauses                    : 33
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 1
% 0.13/0.37  # ...remaining for further processing  : 32
% 0.13/0.37  # Other redundant clauses eliminated   : 1
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 9
% 0.13/0.37  # Generated clauses                    : 16
% 0.13/0.37  # ...of the previous two non-trivial   : 21
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 15
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 1
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
% 0.13/0.37  #    Positive orientable unit clauses  : 4
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 1
% 0.13/0.37  #    Non-unit-clauses                  : 7
% 0.13/0.37  # Current number of unprocessed clauses: 0
% 0.13/0.37  # ...number of literals in the above   : 0
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 19
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 0
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 0
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 1
% 0.13/0.37  # BW rewrite match successes           : 1
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1097
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.027 s
% 0.13/0.37  # System time              : 0.004 s
% 0.13/0.37  # Total time               : 0.031 s
% 0.13/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
