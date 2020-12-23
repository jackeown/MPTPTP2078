%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:40 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 142 expanded)
%              Number of clauses        :   24 (  54 expanded)
%              Number of leaves         :    7 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :  117 ( 514 expanded)
%              Number of equality atoms :   36 ( 206 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ~ ( X2 != k1_xboole_0
          & k7_setfam_1(X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

fof(d8_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( X3 = k7_setfam_1(X1,X2)
          <=> ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(X1))
               => ( r2_hidden(X4,X3)
                <=> r2_hidden(k3_subset_1(X1,X4),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

fof(dt_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ~ ( X2 != k1_xboole_0
            & k7_setfam_1(X1,X2) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t46_setfam_1])).

fof(c_0_8,plain,(
    ! [X13,X14,X15,X16] :
      ( ( ~ r2_hidden(X16,X15)
        | r2_hidden(k3_subset_1(X13,X16),X14)
        | ~ m1_subset_1(X16,k1_zfmisc_1(X13))
        | X15 != k7_setfam_1(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))) )
      & ( ~ r2_hidden(k3_subset_1(X13,X16),X14)
        | r2_hidden(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(X13))
        | X15 != k7_setfam_1(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))) )
      & ( m1_subset_1(esk1_3(X13,X14,X15),k1_zfmisc_1(X13))
        | X15 = k7_setfam_1(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | ~ r2_hidden(k3_subset_1(X13,esk1_3(X13,X14,X15)),X14)
        | X15 = k7_setfam_1(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X15)
        | r2_hidden(k3_subset_1(X13,esk1_3(X13,X14,X15)),X14)
        | X15 = k7_setfam_1(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).

fof(c_0_9,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    & esk3_0 != k1_xboole_0
    & k7_setfam_1(esk2_0,esk3_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X18)))
      | m1_subset_1(k7_setfam_1(X18,X19),k1_zfmisc_1(k1_zfmisc_1(X18))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

cnf(c_0_11,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(X1))
    | X3 = k7_setfam_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X5,X6] :
      ( ( k2_zfmisc_1(X5,X6) != k1_xboole_0
        | X5 = k1_xboole_0
        | X6 = k1_xboole_0 )
      & ( X5 != k1_xboole_0
        | k2_zfmisc_1(X5,X6) = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X5,X6) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_14,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | X4 != k7_setfam_1(X1,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( k7_setfam_1(esk2_0,X1) = esk3_0
    | m1_subset_1(esk1_3(esk2_0,X1,esk3_0),k1_zfmisc_1(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( k7_setfam_1(esk2_0,esk3_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_19,plain,(
    ! [X7,X8] : ~ r2_hidden(X7,k2_zfmisc_1(X7,X8)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_20,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,plain,(
    ! [X9,X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | m1_subset_1(k3_subset_1(X9,X10),k1_zfmisc_1(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_22,plain,(
    ! [X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | k3_subset_1(X11,k3_subset_1(X11,X12)) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k7_setfam_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(k3_subset_1(X2,X1),X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,esk3_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_12]),c_0_17]),c_0_18])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,X3)),X2)
    | X3 = k7_setfam_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,esk3_0,esk3_0),k7_setfam_1(esk2_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    | ~ r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0)),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0)),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( k3_subset_1(esk2_0,k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0))) = esk1_3(esk2_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( k7_setfam_1(esk2_0,X1) = esk3_0
    | r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,X1,esk3_0)),X1)
    | r2_hidden(esk1_3(esk2_0,X1,esk3_0),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_12])).

cnf(c_0_35,negated_conjecture,
    ( ~ r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_12]),c_0_17]),c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0)),k7_setfam_1(esk2_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    | ~ r2_hidden(esk1_3(esk2_0,esk3_0,esk3_0),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_32]),c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,esk3_0,esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_12]),c_0_17]),c_0_18]),c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_12]),c_0_17]),c_0_37])]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:30:54 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S080I
% 0.18/0.37  # and selection function SelectCQIArNXTEqFirst.
% 0.18/0.37  #
% 0.18/0.37  # Preprocessing time       : 0.027 s
% 0.18/0.37  # Presaturation interreduction done
% 0.18/0.37  
% 0.18/0.37  # Proof found!
% 0.18/0.37  # SZS status Theorem
% 0.18/0.37  # SZS output start CNFRefutation
% 0.18/0.37  fof(t46_setfam_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>~((X2!=k1_xboole_0&k7_setfam_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 0.18/0.37  fof(d8_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X3=k7_setfam_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(r2_hidden(X4,X3)<=>r2_hidden(k3_subset_1(X1,X4),X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 0.18/0.37  fof(dt_k7_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 0.18/0.37  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.18/0.37  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.18/0.37  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.18/0.37  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.18/0.37  fof(c_0_7, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>~((X2!=k1_xboole_0&k7_setfam_1(X1,X2)=k1_xboole_0)))), inference(assume_negation,[status(cth)],[t46_setfam_1])).
% 0.18/0.37  fof(c_0_8, plain, ![X13, X14, X15, X16]:(((~r2_hidden(X16,X15)|r2_hidden(k3_subset_1(X13,X16),X14)|~m1_subset_1(X16,k1_zfmisc_1(X13))|X15!=k7_setfam_1(X13,X14)|~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))|~m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))))&(~r2_hidden(k3_subset_1(X13,X16),X14)|r2_hidden(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(X13))|X15!=k7_setfam_1(X13,X14)|~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))|~m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13)))))&((m1_subset_1(esk1_3(X13,X14,X15),k1_zfmisc_1(X13))|X15=k7_setfam_1(X13,X14)|~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))|~m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))))&((~r2_hidden(esk1_3(X13,X14,X15),X15)|~r2_hidden(k3_subset_1(X13,esk1_3(X13,X14,X15)),X14)|X15=k7_setfam_1(X13,X14)|~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))|~m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))))&(r2_hidden(esk1_3(X13,X14,X15),X15)|r2_hidden(k3_subset_1(X13,esk1_3(X13,X14,X15)),X14)|X15=k7_setfam_1(X13,X14)|~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))|~m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).
% 0.18/0.37  fof(c_0_9, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))&(esk3_0!=k1_xboole_0&k7_setfam_1(esk2_0,esk3_0)=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.18/0.37  fof(c_0_10, plain, ![X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X18)))|m1_subset_1(k7_setfam_1(X18,X19),k1_zfmisc_1(k1_zfmisc_1(X18)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).
% 0.18/0.37  cnf(c_0_11, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(X1))|X3=k7_setfam_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.37  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.37  fof(c_0_13, plain, ![X5, X6]:((k2_zfmisc_1(X5,X6)!=k1_xboole_0|(X5=k1_xboole_0|X6=k1_xboole_0))&((X5!=k1_xboole_0|k2_zfmisc_1(X5,X6)=k1_xboole_0)&(X6!=k1_xboole_0|k2_zfmisc_1(X5,X6)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.18/0.37  cnf(c_0_14, plain, (r2_hidden(X2,X4)|~r2_hidden(k3_subset_1(X1,X2),X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|X4!=k7_setfam_1(X1,X3)|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.37  cnf(c_0_15, plain, (m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.37  cnf(c_0_16, negated_conjecture, (k7_setfam_1(esk2_0,X1)=esk3_0|m1_subset_1(esk1_3(esk2_0,X1,esk3_0),k1_zfmisc_1(esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.18/0.37  cnf(c_0_17, negated_conjecture, (k7_setfam_1(esk2_0,esk3_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.37  cnf(c_0_18, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.37  fof(c_0_19, plain, ![X7, X8]:~r2_hidden(X7,k2_zfmisc_1(X7,X8)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.18/0.37  cnf(c_0_20, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.37  fof(c_0_21, plain, ![X9, X10]:(~m1_subset_1(X10,k1_zfmisc_1(X9))|m1_subset_1(k3_subset_1(X9,X10),k1_zfmisc_1(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.18/0.37  fof(c_0_22, plain, ![X11, X12]:(~m1_subset_1(X12,k1_zfmisc_1(X11))|k3_subset_1(X11,k3_subset_1(X11,X12))=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.18/0.37  cnf(c_0_23, plain, (r2_hidden(X1,k7_setfam_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(k3_subset_1(X2,X1),X3)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_14]), c_0_15])).
% 0.18/0.37  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,esk3_0,esk3_0),k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_12]), c_0_17]), c_0_18])).
% 0.18/0.37  cnf(c_0_25, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.37  cnf(c_0_26, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_20])).
% 0.18/0.37  cnf(c_0_27, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.37  cnf(c_0_28, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.37  cnf(c_0_29, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,X3)),X2)|X3=k7_setfam_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.38  cnf(c_0_30, negated_conjecture, (r2_hidden(esk1_3(esk2_0,esk3_0,esk3_0),k7_setfam_1(esk2_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))|~r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0)),X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.18/0.38  cnf(c_0_31, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.18/0.38  cnf(c_0_32, negated_conjecture, (m1_subset_1(k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0)),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_27, c_0_24])).
% 0.18/0.38  cnf(c_0_33, negated_conjecture, (k3_subset_1(esk2_0,k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0)))=esk1_3(esk2_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_28, c_0_24])).
% 0.18/0.38  cnf(c_0_34, negated_conjecture, (k7_setfam_1(esk2_0,X1)=esk3_0|r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,X1,esk3_0)),X1)|r2_hidden(esk1_3(esk2_0,X1,esk3_0),esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(spm,[status(thm)],[c_0_29, c_0_12])).
% 0.18/0.38  cnf(c_0_35, negated_conjecture, (~r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0)),esk3_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_12]), c_0_17]), c_0_31])).
% 0.18/0.38  cnf(c_0_36, negated_conjecture, (r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0)),k7_setfam_1(esk2_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))|~r2_hidden(esk1_3(esk2_0,esk3_0,esk3_0),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_32]), c_0_33])).
% 0.18/0.38  cnf(c_0_37, negated_conjecture, (r2_hidden(esk1_3(esk2_0,esk3_0,esk3_0),esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_12]), c_0_17]), c_0_18]), c_0_35])).
% 0.18/0.38  cnf(c_0_38, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_12]), c_0_17]), c_0_37])]), c_0_31]), ['proof']).
% 0.18/0.38  # SZS output end CNFRefutation
% 0.18/0.38  # Proof object total steps             : 39
% 0.18/0.38  # Proof object clause steps            : 24
% 0.18/0.38  # Proof object formula steps           : 15
% 0.18/0.38  # Proof object conjectures             : 16
% 0.18/0.38  # Proof object clause conjectures      : 13
% 0.18/0.38  # Proof object formula conjectures     : 3
% 0.18/0.38  # Proof object initial clauses used    : 11
% 0.18/0.38  # Proof object initial formulas used   : 7
% 0.18/0.38  # Proof object generating inferences   : 11
% 0.18/0.38  # Proof object simplifying inferences  : 15
% 0.18/0.38  # Training examples: 0 positive, 0 negative
% 0.18/0.38  # Parsed axioms                        : 7
% 0.18/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.38  # Initial clauses                      : 15
% 0.18/0.38  # Removed in clause preprocessing      : 0
% 0.18/0.38  # Initial clauses in saturation        : 15
% 0.18/0.38  # Processed clauses                    : 107
% 0.18/0.38  # ...of these trivial                  : 4
% 0.18/0.38  # ...subsumed                          : 12
% 0.18/0.38  # ...remaining for further processing  : 91
% 0.18/0.38  # Other redundant clauses eliminated   : 4
% 0.18/0.38  # Clauses deleted for lack of memory   : 0
% 0.18/0.38  # Backward-subsumed                    : 0
% 0.18/0.38  # Backward-rewritten                   : 4
% 0.18/0.38  # Generated clauses                    : 502
% 0.18/0.38  # ...of the previous two non-trivial   : 474
% 0.18/0.38  # Contextual simplify-reflections      : 2
% 0.18/0.38  # Paramodulations                      : 498
% 0.18/0.38  # Factorizations                       : 0
% 0.18/0.38  # Equation resolutions                 : 4
% 0.18/0.38  # Propositional unsat checks           : 0
% 0.18/0.38  #    Propositional check models        : 0
% 0.18/0.38  #    Propositional check unsatisfiable : 0
% 0.18/0.38  #    Propositional clauses             : 0
% 0.18/0.38  #    Propositional clauses after purity: 0
% 0.18/0.38  #    Propositional unsat core size     : 0
% 0.18/0.38  #    Propositional preprocessing time  : 0.000
% 0.18/0.38  #    Propositional encoding time       : 0.000
% 0.18/0.38  #    Propositional solver time         : 0.000
% 0.18/0.38  #    Success case prop preproc time    : 0.000
% 0.18/0.38  #    Success case prop encoding time   : 0.000
% 0.18/0.38  #    Success case prop solver time     : 0.000
% 0.18/0.38  # Current number of processed clauses  : 68
% 0.18/0.38  #    Positive orientable unit clauses  : 38
% 0.18/0.38  #    Positive unorientable unit clauses: 0
% 0.18/0.38  #    Negative unit clauses             : 5
% 0.18/0.38  #    Non-unit-clauses                  : 25
% 0.18/0.38  # Current number of unprocessed clauses: 378
% 0.18/0.38  # ...number of literals in the above   : 918
% 0.18/0.38  # Current number of archived formulas  : 0
% 0.18/0.38  # Current number of archived clauses   : 19
% 0.18/0.38  # Clause-clause subsumption calls (NU) : 104
% 0.18/0.38  # Rec. Clause-clause subsumption calls : 37
% 0.18/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.18/0.38  # Unit Clause-clause subsumption calls : 21
% 0.18/0.38  # Rewrite failures with RHS unbound    : 0
% 0.18/0.38  # BW rewrite match attempts            : 83
% 0.18/0.38  # BW rewrite match successes           : 2
% 0.18/0.38  # Condensation attempts                : 0
% 0.18/0.38  # Condensation successes               : 0
% 0.18/0.38  # Termbank termtop insertions          : 20564
% 0.18/0.38  
% 0.18/0.38  # -------------------------------------------------
% 0.18/0.38  # User time                : 0.034 s
% 0.18/0.38  # System time              : 0.007 s
% 0.18/0.38  # Total time               : 0.041 s
% 0.18/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
