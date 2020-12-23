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
% DateTime   : Thu Dec  3 10:47:39 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 148 expanded)
%              Number of clauses        :   27 (  56 expanded)
%              Number of leaves         :    9 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :  120 ( 512 expanded)
%              Number of equality atoms :   37 ( 201 expanded)
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

fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

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

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ~ ( X2 != k1_xboole_0
            & k7_setfam_1(X1,X2) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t46_setfam_1])).

fof(c_0_10,plain,(
    ! [X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X19,X18)
        | r2_hidden(k3_subset_1(X16,X19),X17)
        | ~ m1_subset_1(X19,k1_zfmisc_1(X16))
        | X18 != k7_setfam_1(X16,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X16)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16))) )
      & ( ~ r2_hidden(k3_subset_1(X16,X19),X17)
        | r2_hidden(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(X16))
        | X18 != k7_setfam_1(X16,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X16)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16))) )
      & ( m1_subset_1(esk1_3(X16,X17,X18),k1_zfmisc_1(X16))
        | X18 = k7_setfam_1(X16,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X16)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16))) )
      & ( ~ r2_hidden(esk1_3(X16,X17,X18),X18)
        | ~ r2_hidden(k3_subset_1(X16,esk1_3(X16,X17,X18)),X17)
        | X18 = k7_setfam_1(X16,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X16)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16))) )
      & ( r2_hidden(esk1_3(X16,X17,X18),X18)
        | r2_hidden(k3_subset_1(X16,esk1_3(X16,X17,X18)),X17)
        | X18 = k7_setfam_1(X16,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X16)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).

fof(c_0_11,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    & esk3_0 != k1_xboole_0
    & k7_setfam_1(esk2_0,esk3_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_12,plain,(
    ! [X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X21)))
      | m1_subset_1(k7_setfam_1(X21,X22),k1_zfmisc_1(k1_zfmisc_1(X21))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

fof(c_0_13,plain,(
    ! [X10,X11] : m1_subset_1(k6_subset_1(X10,X11),k1_zfmisc_1(X10)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

fof(c_0_14,plain,(
    ! [X14,X15] : k6_subset_1(X14,X15) = k4_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_15,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(X1))
    | X3 = k7_setfam_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | X4 != k7_setfam_1(X1,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X6,X7] :
      ( ( k4_xboole_0(X6,k1_tarski(X7)) != X6
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(X7,X6)
        | k4_xboole_0(X6,k1_tarski(X7)) = X6 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_22,plain,(
    ! [X5] : k4_xboole_0(k1_xboole_0,X5) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_23,negated_conjecture,
    ( k7_setfam_1(esk2_0,X1) = esk3_0
    | m1_subset_1(esk1_3(esk2_0,X1,esk3_0),k1_zfmisc_1(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( k7_setfam_1(esk2_0,esk3_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k7_setfam_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(k3_subset_1(X2,X1),X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_17]),c_0_18])).

cnf(c_0_27,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | k3_subset_1(X8,X9) = k4_xboole_0(X8,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_31,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(X12))
      | k3_subset_1(X12,k3_subset_1(X12,X13)) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,esk3_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_16]),c_0_24]),c_0_25])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_xboole_0(X1,X2),k7_setfam_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(k3_subset_1(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,X3)),X2)
    | X3 = k7_setfam_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,esk3_0,esk3_0),k7_setfam_1(esk2_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    | ~ r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0)),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(k3_subset_1(esk2_0,k4_xboole_0(esk2_0,X1)),esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_16]),c_0_24]),c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0)) = k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( k3_subset_1(esk2_0,k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0))) = esk1_3(esk2_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( k7_setfam_1(esk2_0,X1) = esk3_0
    | r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,X1,esk3_0)),X1)
    | r2_hidden(esk1_3(esk2_0,X1,esk3_0),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_16])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_16]),c_0_24]),c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(esk1_3(esk2_0,esk3_0,esk3_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_16]),c_0_24]),c_0_25]),c_0_43]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:17:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 0.14/0.40  # and selection function SelectCQIArEqFirst.
% 0.14/0.40  #
% 0.14/0.40  # Preprocessing time       : 0.027 s
% 0.14/0.40  # Presaturation interreduction done
% 0.14/0.40  
% 0.14/0.40  # Proof found!
% 0.14/0.40  # SZS status Theorem
% 0.14/0.40  # SZS output start CNFRefutation
% 0.14/0.40  fof(t46_setfam_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>~((X2!=k1_xboole_0&k7_setfam_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 0.14/0.40  fof(d8_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X3=k7_setfam_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(r2_hidden(X4,X3)<=>r2_hidden(k3_subset_1(X1,X4),X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 0.14/0.40  fof(dt_k7_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 0.14/0.40  fof(dt_k6_subset_1, axiom, ![X1, X2]:m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 0.14/0.40  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.14/0.40  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.14/0.40  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.14/0.40  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.14/0.40  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.14/0.40  fof(c_0_9, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>~((X2!=k1_xboole_0&k7_setfam_1(X1,X2)=k1_xboole_0)))), inference(assume_negation,[status(cth)],[t46_setfam_1])).
% 0.14/0.40  fof(c_0_10, plain, ![X16, X17, X18, X19]:(((~r2_hidden(X19,X18)|r2_hidden(k3_subset_1(X16,X19),X17)|~m1_subset_1(X19,k1_zfmisc_1(X16))|X18!=k7_setfam_1(X16,X17)|~m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X16)))|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16))))&(~r2_hidden(k3_subset_1(X16,X19),X17)|r2_hidden(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(X16))|X18!=k7_setfam_1(X16,X17)|~m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X16)))|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16)))))&((m1_subset_1(esk1_3(X16,X17,X18),k1_zfmisc_1(X16))|X18=k7_setfam_1(X16,X17)|~m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X16)))|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16))))&((~r2_hidden(esk1_3(X16,X17,X18),X18)|~r2_hidden(k3_subset_1(X16,esk1_3(X16,X17,X18)),X17)|X18=k7_setfam_1(X16,X17)|~m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X16)))|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16))))&(r2_hidden(esk1_3(X16,X17,X18),X18)|r2_hidden(k3_subset_1(X16,esk1_3(X16,X17,X18)),X17)|X18=k7_setfam_1(X16,X17)|~m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X16)))|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).
% 0.14/0.40  fof(c_0_11, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))&(esk3_0!=k1_xboole_0&k7_setfam_1(esk2_0,esk3_0)=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.14/0.40  fof(c_0_12, plain, ![X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X21)))|m1_subset_1(k7_setfam_1(X21,X22),k1_zfmisc_1(k1_zfmisc_1(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).
% 0.14/0.40  fof(c_0_13, plain, ![X10, X11]:m1_subset_1(k6_subset_1(X10,X11),k1_zfmisc_1(X10)), inference(variable_rename,[status(thm)],[dt_k6_subset_1])).
% 0.14/0.40  fof(c_0_14, plain, ![X14, X15]:k6_subset_1(X14,X15)=k4_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.14/0.40  cnf(c_0_15, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(X1))|X3=k7_setfam_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.40  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.40  cnf(c_0_17, plain, (r2_hidden(X2,X4)|~r2_hidden(k3_subset_1(X1,X2),X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|X4!=k7_setfam_1(X1,X3)|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.40  cnf(c_0_18, plain, (m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.40  cnf(c_0_19, plain, (m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.40  cnf(c_0_20, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.40  fof(c_0_21, plain, ![X6, X7]:((k4_xboole_0(X6,k1_tarski(X7))!=X6|~r2_hidden(X7,X6))&(r2_hidden(X7,X6)|k4_xboole_0(X6,k1_tarski(X7))=X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.14/0.40  fof(c_0_22, plain, ![X5]:k4_xboole_0(k1_xboole_0,X5)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.14/0.40  cnf(c_0_23, negated_conjecture, (k7_setfam_1(esk2_0,X1)=esk3_0|m1_subset_1(esk1_3(esk2_0,X1,esk3_0),k1_zfmisc_1(esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.14/0.40  cnf(c_0_24, negated_conjecture, (k7_setfam_1(esk2_0,esk3_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.40  cnf(c_0_25, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.40  cnf(c_0_26, plain, (r2_hidden(X1,k7_setfam_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(k3_subset_1(X2,X1),X3)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_17]), c_0_18])).
% 0.14/0.40  cnf(c_0_27, plain, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.14/0.40  cnf(c_0_28, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.40  cnf(c_0_29, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.40  fof(c_0_30, plain, ![X8, X9]:(~m1_subset_1(X9,k1_zfmisc_1(X8))|k3_subset_1(X8,X9)=k4_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.14/0.40  fof(c_0_31, plain, ![X12, X13]:(~m1_subset_1(X13,k1_zfmisc_1(X12))|k3_subset_1(X12,k3_subset_1(X12,X13))=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.14/0.40  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,esk3_0,esk3_0),k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_16]), c_0_24]), c_0_25])).
% 0.14/0.40  cnf(c_0_33, plain, (r2_hidden(k4_xboole_0(X1,X2),k7_setfam_1(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~r2_hidden(k3_subset_1(X1,k4_xboole_0(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.14/0.40  cnf(c_0_34, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.14/0.40  cnf(c_0_35, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.40  cnf(c_0_36, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.40  cnf(c_0_37, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,X3)),X2)|X3=k7_setfam_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.40  cnf(c_0_38, negated_conjecture, (r2_hidden(esk1_3(esk2_0,esk3_0,esk3_0),k7_setfam_1(esk2_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))|~r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0)),X1)), inference(spm,[status(thm)],[c_0_26, c_0_32])).
% 0.14/0.40  cnf(c_0_39, negated_conjecture, (~r2_hidden(k3_subset_1(esk2_0,k4_xboole_0(esk2_0,X1)),esk3_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_16]), c_0_24]), c_0_34])).
% 0.14/0.40  cnf(c_0_40, negated_conjecture, (k4_xboole_0(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0))=k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_35, c_0_32])).
% 0.14/0.40  cnf(c_0_41, negated_conjecture, (k3_subset_1(esk2_0,k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0)))=esk1_3(esk2_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_36, c_0_32])).
% 0.14/0.40  cnf(c_0_42, negated_conjecture, (k7_setfam_1(esk2_0,X1)=esk3_0|r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,X1,esk3_0)),X1)|r2_hidden(esk1_3(esk2_0,X1,esk3_0),esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(spm,[status(thm)],[c_0_37, c_0_16])).
% 0.14/0.40  cnf(c_0_43, negated_conjecture, (~r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0)),esk3_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_16]), c_0_24]), c_0_34])).
% 0.14/0.40  cnf(c_0_44, negated_conjecture, (~r2_hidden(esk1_3(esk2_0,esk3_0,esk3_0),esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.14/0.40  cnf(c_0_45, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_16]), c_0_24]), c_0_25]), c_0_43]), c_0_44]), ['proof']).
% 0.14/0.40  # SZS output end CNFRefutation
% 0.14/0.40  # Proof object total steps             : 46
% 0.14/0.40  # Proof object clause steps            : 27
% 0.14/0.40  # Proof object formula steps           : 19
% 0.14/0.40  # Proof object conjectures             : 16
% 0.14/0.40  # Proof object clause conjectures      : 13
% 0.14/0.40  # Proof object formula conjectures     : 3
% 0.14/0.40  # Proof object initial clauses used    : 13
% 0.14/0.40  # Proof object initial formulas used   : 9
% 0.14/0.40  # Proof object generating inferences   : 12
% 0.14/0.40  # Proof object simplifying inferences  : 14
% 0.14/0.40  # Training examples: 0 positive, 0 negative
% 0.14/0.40  # Parsed axioms                        : 10
% 0.14/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.40  # Initial clauses                      : 17
% 0.14/0.40  # Removed in clause preprocessing      : 1
% 0.14/0.40  # Initial clauses in saturation        : 16
% 0.14/0.40  # Processed clauses                    : 215
% 0.14/0.40  # ...of these trivial                  : 4
% 0.14/0.40  # ...subsumed                          : 36
% 0.14/0.40  # ...remaining for further processing  : 175
% 0.14/0.40  # Other redundant clauses eliminated   : 2
% 0.14/0.40  # Clauses deleted for lack of memory   : 0
% 0.14/0.40  # Backward-subsumed                    : 4
% 0.14/0.40  # Backward-rewritten                   : 6
% 0.14/0.40  # Generated clauses                    : 1140
% 0.14/0.40  # ...of the previous two non-trivial   : 781
% 0.14/0.40  # Contextual simplify-reflections      : 4
% 0.14/0.40  # Paramodulations                      : 1138
% 0.14/0.40  # Factorizations                       : 0
% 0.14/0.40  # Equation resolutions                 : 2
% 0.14/0.40  # Propositional unsat checks           : 0
% 0.14/0.40  #    Propositional check models        : 0
% 0.14/0.40  #    Propositional check unsatisfiable : 0
% 0.14/0.40  #    Propositional clauses             : 0
% 0.14/0.40  #    Propositional clauses after purity: 0
% 0.14/0.40  #    Propositional unsat core size     : 0
% 0.14/0.40  #    Propositional preprocessing time  : 0.000
% 0.14/0.40  #    Propositional encoding time       : 0.000
% 0.14/0.40  #    Propositional solver time         : 0.000
% 0.14/0.40  #    Success case prop preproc time    : 0.000
% 0.14/0.40  #    Success case prop encoding time   : 0.000
% 0.14/0.40  #    Success case prop solver time     : 0.000
% 0.14/0.40  # Current number of processed clauses  : 147
% 0.14/0.40  #    Positive orientable unit clauses  : 53
% 0.14/0.40  #    Positive unorientable unit clauses: 0
% 0.14/0.40  #    Negative unit clauses             : 8
% 0.14/0.40  #    Non-unit-clauses                  : 86
% 0.14/0.40  # Current number of unprocessed clauses: 567
% 0.14/0.40  # ...number of literals in the above   : 1363
% 0.14/0.40  # Current number of archived formulas  : 0
% 0.14/0.40  # Current number of archived clauses   : 27
% 0.14/0.40  # Clause-clause subsumption calls (NU) : 648
% 0.14/0.40  # Rec. Clause-clause subsumption calls : 453
% 0.14/0.40  # Non-unit clause-clause subsumptions  : 22
% 0.14/0.40  # Unit Clause-clause subsumption calls : 122
% 0.14/0.40  # Rewrite failures with RHS unbound    : 0
% 0.14/0.40  # BW rewrite match attempts            : 163
% 0.14/0.40  # BW rewrite match successes           : 6
% 0.14/0.40  # Condensation attempts                : 0
% 0.14/0.40  # Condensation successes               : 0
% 0.14/0.40  # Termbank termtop insertions          : 35764
% 0.14/0.40  
% 0.14/0.40  # -------------------------------------------------
% 0.14/0.40  # User time                : 0.051 s
% 0.14/0.40  # System time              : 0.004 s
% 0.14/0.40  # Total time               : 0.055 s
% 0.14/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
