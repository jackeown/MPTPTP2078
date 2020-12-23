%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:59 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 (  70 expanded)
%              Number of clauses        :   25 (  30 expanded)
%              Number of leaves         :   11 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :  107 ( 162 expanded)
%              Number of equality atoms :   41 (  71 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
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

fof(t49_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r2_hidden(k3_subset_1(X1,X3),k7_setfam_1(X1,X2))
          <=> r2_hidden(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_setfam_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

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

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ( X2 != k1_xboole_0
         => k5_setfam_1(X1,k7_setfam_1(X1,X2)) = k3_subset_1(X1,k6_setfam_1(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t12_tops_2])).

fof(c_0_12,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14)))
      | m1_subset_1(k7_setfam_1(X14,X15),k1_zfmisc_1(k1_zfmisc_1(X14))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

fof(c_0_13,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    & esk3_0 != k1_xboole_0
    & k5_setfam_1(esk2_0,k7_setfam_1(esk2_0,esk3_0)) != k3_subset_1(esk2_0,k6_setfam_1(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_14,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12)))
      | m1_subset_1(k5_setfam_1(X12,X13),k1_zfmisc_1(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).

cnf(c_0_15,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16)))
      | k7_setfam_1(X16,k7_setfam_1(X16,X17)) = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).

fof(c_0_18,plain,(
    ! [X18,X19,X20] :
      ( ( ~ r2_hidden(k3_subset_1(X18,X20),k7_setfam_1(X18,X19))
        | r2_hidden(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X18))) )
      & ( ~ r2_hidden(X20,X19)
        | r2_hidden(k3_subset_1(X18,X20),k7_setfam_1(X18,X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_setfam_1])])])])).

fof(c_0_19,plain,(
    ! [X21,X22,X23] :
      ( ~ r2_hidden(X21,X22)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X23))
      | m1_subset_1(X21,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_20,plain,(
    ! [X4] :
      ( X4 = k1_xboole_0
      | r2_hidden(esk1_1(X4),X4) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_21,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | k3_subset_1(X10,k3_subset_1(X10,X11)) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_22,plain,
    ( m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(k7_setfam_1(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_24,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24)))
      | X25 = k1_xboole_0
      | k6_setfam_1(X24,k7_setfam_1(X24,X25)) = k3_subset_1(X24,k5_setfam_1(X24,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tops_2])])).

cnf(c_0_25,plain,
    ( k7_setfam_1(X2,k7_setfam_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_26,plain,(
    ! [X6,X7] :
      ( ( k2_zfmisc_1(X6,X7) != k1_xboole_0
        | X6 = k1_xboole_0
        | X7 = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_27,plain,
    ( r2_hidden(k3_subset_1(X3,X1),k7_setfam_1(X3,X2))
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(k5_setfam_1(esk2_0,k7_setfam_1(esk2_0,esk3_0)),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_33,plain,
    ( X1 = k1_xboole_0
    | k6_setfam_1(X2,k7_setfam_1(X2,X1)) = k3_subset_1(X2,k5_setfam_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( k7_setfam_1(esk2_0,k7_setfam_1(esk2_0,esk3_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_16])).

fof(c_0_35,plain,(
    ! [X8,X9] : ~ r2_hidden(X8,k2_zfmisc_1(X8,X9)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X2,X3) ),
    inference(csr,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk1_1(esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( k3_subset_1(esk2_0,k3_subset_1(esk2_0,k5_setfam_1(esk2_0,k7_setfam_1(esk2_0,esk3_0)))) = k5_setfam_1(esk2_0,k7_setfam_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( k3_subset_1(esk2_0,k5_setfam_1(esk2_0,k7_setfam_1(esk2_0,esk3_0))) = k6_setfam_1(esk2_0,esk3_0)
    | k7_setfam_1(esk2_0,esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_23]),c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( k5_setfam_1(esk2_0,k7_setfam_1(esk2_0,esk3_0)) != k3_subset_1(esk2_0,k6_setfam_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k3_subset_1(X1,esk1_1(esk3_0)),k7_setfam_1(X1,esk3_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( k7_setfam_1(esk2_0,esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_16]),c_0_45]),c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:18:45 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  # Version: 2.5pre002
% 0.20/0.34  # No SInE strategy applied
% 0.20/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00DA
% 0.20/0.40  # and selection function SelectSmallestOrientable.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.028 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t12_tops_2, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X2!=k1_xboole_0=>k5_setfam_1(X1,k7_setfam_1(X1,X2))=k3_subset_1(X1,k6_setfam_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tops_2)).
% 0.20/0.40  fof(dt_k7_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 0.20/0.40  fof(dt_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 0.20/0.40  fof(involutiveness_k7_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k7_setfam_1(X1,k7_setfam_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 0.20/0.40  fof(t49_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r2_hidden(k3_subset_1(X1,X3),k7_setfam_1(X1,X2))<=>r2_hidden(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_setfam_1)).
% 0.20/0.40  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.20/0.40  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.20/0.40  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.20/0.40  fof(t11_tops_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X2!=k1_xboole_0=>k6_setfam_1(X1,k7_setfam_1(X1,X2))=k3_subset_1(X1,k5_setfam_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tops_2)).
% 0.20/0.40  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.40  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.20/0.40  fof(c_0_11, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X2!=k1_xboole_0=>k5_setfam_1(X1,k7_setfam_1(X1,X2))=k3_subset_1(X1,k6_setfam_1(X1,X2))))), inference(assume_negation,[status(cth)],[t12_tops_2])).
% 0.20/0.40  fof(c_0_12, plain, ![X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14)))|m1_subset_1(k7_setfam_1(X14,X15),k1_zfmisc_1(k1_zfmisc_1(X14)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).
% 0.20/0.40  fof(c_0_13, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))&(esk3_0!=k1_xboole_0&k5_setfam_1(esk2_0,k7_setfam_1(esk2_0,esk3_0))!=k3_subset_1(esk2_0,k6_setfam_1(esk2_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.20/0.40  fof(c_0_14, plain, ![X12, X13]:(~m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12)))|m1_subset_1(k5_setfam_1(X12,X13),k1_zfmisc_1(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).
% 0.20/0.40  cnf(c_0_15, plain, (m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  fof(c_0_17, plain, ![X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16)))|k7_setfam_1(X16,k7_setfam_1(X16,X17))=X17), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).
% 0.20/0.40  fof(c_0_18, plain, ![X18, X19, X20]:((~r2_hidden(k3_subset_1(X18,X20),k7_setfam_1(X18,X19))|r2_hidden(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(X18))|~m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X18))))&(~r2_hidden(X20,X19)|r2_hidden(k3_subset_1(X18,X20),k7_setfam_1(X18,X19))|~m1_subset_1(X20,k1_zfmisc_1(X18))|~m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_setfam_1])])])])).
% 0.20/0.40  fof(c_0_19, plain, ![X21, X22, X23]:(~r2_hidden(X21,X22)|~m1_subset_1(X22,k1_zfmisc_1(X23))|m1_subset_1(X21,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.20/0.40  fof(c_0_20, plain, ![X4]:(X4=k1_xboole_0|r2_hidden(esk1_1(X4),X4)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.20/0.40  fof(c_0_21, plain, ![X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(X10))|k3_subset_1(X10,k3_subset_1(X10,X11))=X11), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.20/0.40  cnf(c_0_22, plain, (m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.40  cnf(c_0_23, negated_conjecture, (m1_subset_1(k7_setfam_1(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.40  fof(c_0_24, plain, ![X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24)))|(X25=k1_xboole_0|k6_setfam_1(X24,k7_setfam_1(X24,X25))=k3_subset_1(X24,k5_setfam_1(X24,X25)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tops_2])])).
% 0.20/0.40  cnf(c_0_25, plain, (k7_setfam_1(X2,k7_setfam_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  fof(c_0_26, plain, ![X6, X7]:((k2_zfmisc_1(X6,X7)!=k1_xboole_0|(X6=k1_xboole_0|X7=k1_xboole_0))&((X6!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0)&(X7!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.40  cnf(c_0_27, plain, (r2_hidden(k3_subset_1(X3,X1),k7_setfam_1(X3,X2))|~r2_hidden(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.40  cnf(c_0_28, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.40  cnf(c_0_29, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  cnf(c_0_30, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.40  cnf(c_0_31, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.40  cnf(c_0_32, negated_conjecture, (m1_subset_1(k5_setfam_1(esk2_0,k7_setfam_1(esk2_0,esk3_0)),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.40  cnf(c_0_33, plain, (X1=k1_xboole_0|k6_setfam_1(X2,k7_setfam_1(X2,X1))=k3_subset_1(X2,k5_setfam_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.40  cnf(c_0_34, negated_conjecture, (k7_setfam_1(esk2_0,k7_setfam_1(esk2_0,esk3_0))=esk3_0), inference(spm,[status(thm)],[c_0_25, c_0_16])).
% 0.20/0.40  fof(c_0_35, plain, ![X8, X9]:~r2_hidden(X8,k2_zfmisc_1(X8,X9)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.20/0.40  cnf(c_0_36, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.40  cnf(c_0_37, plain, (r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~r2_hidden(X2,X3)), inference(csr,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.40  cnf(c_0_38, negated_conjecture, (r2_hidden(esk1_1(esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.40  cnf(c_0_39, negated_conjecture, (k3_subset_1(esk2_0,k3_subset_1(esk2_0,k5_setfam_1(esk2_0,k7_setfam_1(esk2_0,esk3_0))))=k5_setfam_1(esk2_0,k7_setfam_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.40  cnf(c_0_40, negated_conjecture, (k3_subset_1(esk2_0,k5_setfam_1(esk2_0,k7_setfam_1(esk2_0,esk3_0)))=k6_setfam_1(esk2_0,esk3_0)|k7_setfam_1(esk2_0,esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_23]), c_0_34])).
% 0.20/0.40  cnf(c_0_41, negated_conjecture, (k5_setfam_1(esk2_0,k7_setfam_1(esk2_0,esk3_0))!=k3_subset_1(esk2_0,k6_setfam_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  cnf(c_0_42, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.40  cnf(c_0_43, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_36])).
% 0.20/0.40  cnf(c_0_44, negated_conjecture, (r2_hidden(k3_subset_1(X1,esk1_1(esk3_0)),k7_setfam_1(X1,esk3_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.40  cnf(c_0_45, negated_conjecture, (k7_setfam_1(esk2_0,esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.20/0.40  cnf(c_0_46, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.40  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_16]), c_0_45]), c_0_46]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 48
% 0.20/0.40  # Proof object clause steps            : 25
% 0.20/0.40  # Proof object formula steps           : 23
% 0.20/0.40  # Proof object conjectures             : 15
% 0.20/0.40  # Proof object clause conjectures      : 12
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 13
% 0.20/0.40  # Proof object initial formulas used   : 11
% 0.20/0.40  # Proof object generating inferences   : 10
% 0.20/0.40  # Proof object simplifying inferences  : 6
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 11
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 16
% 0.20/0.40  # Removed in clause preprocessing      : 0
% 0.20/0.40  # Initial clauses in saturation        : 16
% 0.20/0.40  # Processed clauses                    : 253
% 0.20/0.40  # ...of these trivial                  : 5
% 0.20/0.40  # ...subsumed                          : 139
% 0.20/0.40  # ...remaining for further processing  : 109
% 0.20/0.40  # Other redundant clauses eliminated   : 20
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 0
% 0.20/0.40  # Backward-rewritten                   : 10
% 0.20/0.40  # Generated clauses                    : 1891
% 0.20/0.40  # ...of the previous two non-trivial   : 1691
% 0.20/0.40  # Contextual simplify-reflections      : 1
% 0.20/0.40  # Paramodulations                      : 1863
% 0.20/0.40  # Factorizations                       : 8
% 0.20/0.40  # Equation resolutions                 : 20
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 81
% 0.20/0.40  #    Positive orientable unit clauses  : 16
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 5
% 0.20/0.40  #    Non-unit-clauses                  : 60
% 0.20/0.40  # Current number of unprocessed clauses: 1449
% 0.20/0.40  # ...number of literals in the above   : 4582
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 26
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 548
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 501
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 132
% 0.20/0.40  # Unit Clause-clause subsumption calls : 13
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 3
% 0.20/0.40  # BW rewrite match successes           : 2
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 25769
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.049 s
% 0.20/0.40  # System time              : 0.006 s
% 0.20/0.40  # Total time               : 0.055 s
% 0.20/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
