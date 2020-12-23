%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:56 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   36 (  46 expanded)
%              Number of clauses        :   19 (  20 expanded)
%              Number of leaves         :    8 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :   73 ( 101 expanded)
%              Number of equality atoms :   34 (  52 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t47_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( X2 != k1_xboole_0
       => k7_subset_1(X1,k2_subset_1(X1),k5_setfam_1(X1,X2)) = k6_setfam_1(X1,k7_setfam_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_setfam_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t11_tops_2,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( X2 != k1_xboole_0
       => k6_setfam_1(X1,k7_setfam_1(X1,X2)) = k3_subset_1(X1,k5_setfam_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tops_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(dt_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(c_0_8,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_9,plain,(
    ! [X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16)))
      | X17 = k1_xboole_0
      | k7_subset_1(X16,k2_subset_1(X16),k5_setfam_1(X16,X17)) = k6_setfam_1(X16,k7_setfam_1(X16,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_setfam_1])])).

fof(c_0_10,plain,(
    ! [X6] : k2_subset_1(X6) = X6 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ( X2 != k1_xboole_0
         => k6_setfam_1(X1,k7_setfam_1(X1,X2)) = k3_subset_1(X1,k5_setfam_1(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t11_tops_2])).

fof(c_0_12,plain,(
    ! [X14,X15] :
      ( ( ~ m1_subset_1(X14,k1_zfmisc_1(X15))
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | m1_subset_1(X14,k1_zfmisc_1(X15)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( X1 = k1_xboole_0
    | k7_subset_1(X2,k2_subset_1(X2),k5_setfam_1(X2,X1)) = k6_setfam_1(X2,k7_setfam_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    & esk2_0 != k1_xboole_0
    & k6_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)) != k3_subset_1(esk1_0,k5_setfam_1(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_17,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | k7_subset_1(X9,X10,X11) = k4_xboole_0(X10,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( X1 = k1_xboole_0
    | k7_subset_1(X2,X2,k5_setfam_1(X2,X1)) = k6_setfam_1(X2,k7_setfam_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_25,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12)))
      | m1_subset_1(k5_setfam_1(X12,X13),k1_zfmisc_1(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).

cnf(c_0_26,negated_conjecture,
    ( k7_subset_1(esk1_0,esk1_0,k5_setfam_1(esk1_0,esk2_0)) = k6_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_27,plain,
    ( k7_subset_1(X1,X1,X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_28,plain,(
    ! [X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | k3_subset_1(X7,X8) = k4_xboole_0(X7,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_29,plain,
    ( m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( k6_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)) != k3_subset_1(esk1_0,k5_setfam_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( k6_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)) = k4_xboole_0(esk1_0,k5_setfam_1(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(k5_setfam_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( k3_subset_1(esk1_0,k5_setfam_1(esk1_0,esk2_0)) != k4_xboole_0(esk1_0,k5_setfam_1(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:42:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05EA
% 0.19/0.38  # and selection function SelectDivPreferIntoLits.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.037 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.38  fof(t47_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X2!=k1_xboole_0=>k7_subset_1(X1,k2_subset_1(X1),k5_setfam_1(X1,X2))=k6_setfam_1(X1,k7_setfam_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_setfam_1)).
% 0.19/0.38  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.19/0.38  fof(t11_tops_2, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X2!=k1_xboole_0=>k6_setfam_1(X1,k7_setfam_1(X1,X2))=k3_subset_1(X1,k5_setfam_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tops_2)).
% 0.19/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.38  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.19/0.38  fof(dt_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 0.19/0.38  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.19/0.38  fof(c_0_8, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.38  fof(c_0_9, plain, ![X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16)))|(X17=k1_xboole_0|k7_subset_1(X16,k2_subset_1(X16),k5_setfam_1(X16,X17))=k6_setfam_1(X16,k7_setfam_1(X16,X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_setfam_1])])).
% 0.19/0.38  fof(c_0_10, plain, ![X6]:k2_subset_1(X6)=X6, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.19/0.38  fof(c_0_11, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X2!=k1_xboole_0=>k6_setfam_1(X1,k7_setfam_1(X1,X2))=k3_subset_1(X1,k5_setfam_1(X1,X2))))), inference(assume_negation,[status(cth)],[t11_tops_2])).
% 0.19/0.38  fof(c_0_12, plain, ![X14, X15]:((~m1_subset_1(X14,k1_zfmisc_1(X15))|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|m1_subset_1(X14,k1_zfmisc_1(X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.38  cnf(c_0_13, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.38  cnf(c_0_14, plain, (X1=k1_xboole_0|k7_subset_1(X2,k2_subset_1(X2),k5_setfam_1(X2,X1))=k6_setfam_1(X2,k7_setfam_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_15, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  fof(c_0_16, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))&(esk2_0!=k1_xboole_0&k6_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))!=k3_subset_1(esk1_0,k5_setfam_1(esk1_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.19/0.38  fof(c_0_17, plain, ![X9, X10, X11]:(~m1_subset_1(X10,k1_zfmisc_1(X9))|k7_subset_1(X9,X10,X11)=k4_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.19/0.38  cnf(c_0_18, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_19, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_20, plain, (X1=k1_xboole_0|k7_subset_1(X2,X2,k5_setfam_1(X2,X1))=k6_setfam_1(X2,k7_setfam_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.38  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_22, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_23, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.38  cnf(c_0_24, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.38  fof(c_0_25, plain, ![X12, X13]:(~m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12)))|m1_subset_1(k5_setfam_1(X12,X13),k1_zfmisc_1(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).
% 0.19/0.38  cnf(c_0_26, negated_conjecture, (k7_subset_1(esk1_0,esk1_0,k5_setfam_1(esk1_0,esk2_0))=k6_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.19/0.38  cnf(c_0_27, plain, (k7_subset_1(X1,X1,X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.38  fof(c_0_28, plain, ![X7, X8]:(~m1_subset_1(X8,k1_zfmisc_1(X7))|k3_subset_1(X7,X8)=k4_xboole_0(X7,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.19/0.38  cnf(c_0_29, plain, (m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.38  cnf(c_0_30, negated_conjecture, (k6_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))!=k3_subset_1(esk1_0,k5_setfam_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (k6_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))=k4_xboole_0(esk1_0,k5_setfam_1(esk1_0,esk2_0))), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.38  cnf(c_0_32, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (m1_subset_1(k5_setfam_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_29, c_0_21])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (k3_subset_1(esk1_0,k5_setfam_1(esk1_0,esk2_0))!=k4_xboole_0(esk1_0,k5_setfam_1(esk1_0,esk2_0))), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 36
% 0.19/0.38  # Proof object clause steps            : 19
% 0.19/0.38  # Proof object formula steps           : 17
% 0.19/0.38  # Proof object conjectures             : 11
% 0.19/0.38  # Proof object clause conjectures      : 8
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 10
% 0.19/0.38  # Proof object initial formulas used   : 8
% 0.19/0.38  # Proof object generating inferences   : 5
% 0.19/0.38  # Proof object simplifying inferences  : 6
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 8
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 13
% 0.19/0.38  # Removed in clause preprocessing      : 1
% 0.19/0.38  # Initial clauses in saturation        : 12
% 0.19/0.38  # Processed clauses                    : 35
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 0
% 0.19/0.38  # ...remaining for further processing  : 34
% 0.19/0.38  # Other redundant clauses eliminated   : 2
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 3
% 0.19/0.38  # Generated clauses                    : 18
% 0.19/0.38  # ...of the previous two non-trivial   : 18
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 16
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 2
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
% 0.19/0.38  # Current number of processed clauses  : 18
% 0.19/0.38  #    Positive orientable unit clauses  : 9
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 2
% 0.19/0.38  #    Non-unit-clauses                  : 7
% 0.19/0.38  # Current number of unprocessed clauses: 6
% 0.19/0.38  # ...number of literals in the above   : 9
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 15
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 0
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.38  # Unit Clause-clause subsumption calls : 6
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 13
% 0.19/0.38  # BW rewrite match successes           : 3
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 987
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.036 s
% 0.19/0.38  # System time              : 0.006 s
% 0.19/0.38  # Total time               : 0.042 s
% 0.19/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
