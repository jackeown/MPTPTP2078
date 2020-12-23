%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:45 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   44 (  96 expanded)
%              Number of clauses        :   27 (  40 expanded)
%              Number of leaves         :    8 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :   85 ( 212 expanded)
%              Number of equality atoms :   35 (  68 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k3_subset_1(X1,k7_subset_1(X1,X2,X3)) = k4_subset_1(X1,k3_subset_1(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

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

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => k3_subset_1(X1,k7_subset_1(X1,X2,X3)) = k4_subset_1(X1,k3_subset_1(X1,X2),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t33_subset_1])).

fof(c_0_9,plain,(
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(X16))
      | ~ m1_subset_1(X18,k1_zfmisc_1(X16))
      | k4_subset_1(X16,X17,X18) = k2_xboole_0(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

fof(c_0_10,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
    & k3_subset_1(esk1_0,k7_subset_1(esk1_0,esk2_0,esk3_0)) != k4_subset_1(esk1_0,k3_subset_1(esk1_0,esk2_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | k3_subset_1(X7,X8) = k4_xboole_0(X7,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_12,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | ~ m1_subset_1(X13,k1_zfmisc_1(X11))
      | m1_subset_1(k4_subset_1(X11,X12,X13),k1_zfmisc_1(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

cnf(c_0_13,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X9,X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | m1_subset_1(k3_subset_1(X9,X10),k1_zfmisc_1(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_16,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | k3_subset_1(X14,k3_subset_1(X14,X15)) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_17,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( k2_xboole_0(X1,esk3_0) = k4_subset_1(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k4_subset_1(X1,X2,X3)) = k3_subset_1(X1,k4_subset_1(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_23,plain,(
    ! [X4,X5,X6] : k4_xboole_0(k4_xboole_0(X4,X5),X6) = k4_xboole_0(X4,k2_xboole_0(X5,X6)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_24,negated_conjecture,
    ( k2_xboole_0(k3_subset_1(esk1_0,X1),esk3_0) = k4_subset_1(esk1_0,k3_subset_1(esk1_0,X1),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_26,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(X19))
      | k7_subset_1(X19,X20,X21) = k4_xboole_0(X20,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_27,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,k4_subset_1(X1,X2,X3))) = k4_subset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_subset_1(esk1_0,X1,esk3_0)) = k3_subset_1(esk1_0,k4_subset_1(esk1_0,X1,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_14])).

cnf(c_0_29,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( k2_xboole_0(k3_subset_1(esk1_0,esk2_0),esk3_0) = k4_subset_1(esk1_0,k3_subset_1(esk1_0,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k3_subset_1(X1,X2)) = k3_subset_1(X1,k3_subset_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_25])).

cnf(c_0_33,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( k3_subset_1(esk1_0,k3_subset_1(esk1_0,k4_subset_1(esk1_0,X1,esk3_0))) = k4_subset_1(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_subset_1(esk1_0,k3_subset_1(esk1_0,X1),esk3_0)) = k3_subset_1(esk1_0,k4_subset_1(esk1_0,k3_subset_1(esk1_0,X1),esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_20])).

cnf(c_0_36,negated_conjecture,
    ( k4_xboole_0(X1,k4_subset_1(esk1_0,k3_subset_1(esk1_0,esk2_0),esk3_0)) = k4_xboole_0(k4_xboole_0(X1,k3_subset_1(esk1_0,esk2_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( k4_xboole_0(esk1_0,k3_subset_1(esk1_0,esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_25]),c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( k3_subset_1(esk1_0,k7_subset_1(esk1_0,esk2_0,esk3_0)) != k4_subset_1(esk1_0,k3_subset_1(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_39,negated_conjecture,
    ( k7_subset_1(esk1_0,esk2_0,X1) = k4_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_25])).

cnf(c_0_40,negated_conjecture,
    ( k3_subset_1(esk1_0,k3_subset_1(esk1_0,k4_subset_1(esk1_0,k3_subset_1(esk1_0,X1),esk3_0))) = k4_subset_1(esk1_0,k3_subset_1(esk1_0,X1),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_20])).

cnf(c_0_41,negated_conjecture,
    ( k3_subset_1(esk1_0,k4_subset_1(esk1_0,k3_subset_1(esk1_0,esk2_0),esk3_0)) = k4_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_25]),c_0_36]),c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( k4_subset_1(esk1_0,k3_subset_1(esk1_0,esk2_0),esk3_0) != k3_subset_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_25]),c_0_41]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:06:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S087N
% 0.19/0.40  # and selection function SelectCQArNpEqFirstUnlessPDom.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.028 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t33_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k3_subset_1(X1,k7_subset_1(X1,X2,X3))=k4_subset_1(X1,k3_subset_1(X1,X2),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_subset_1)).
% 0.19/0.40  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.19/0.40  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.19/0.40  fof(dt_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 0.19/0.40  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.19/0.40  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.19/0.40  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.19/0.40  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.19/0.40  fof(c_0_8, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k3_subset_1(X1,k7_subset_1(X1,X2,X3))=k4_subset_1(X1,k3_subset_1(X1,X2),X3)))), inference(assume_negation,[status(cth)],[t33_subset_1])).
% 0.19/0.40  fof(c_0_9, plain, ![X16, X17, X18]:(~m1_subset_1(X17,k1_zfmisc_1(X16))|~m1_subset_1(X18,k1_zfmisc_1(X16))|k4_subset_1(X16,X17,X18)=k2_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.19/0.40  fof(c_0_10, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))&k3_subset_1(esk1_0,k7_subset_1(esk1_0,esk2_0,esk3_0))!=k4_subset_1(esk1_0,k3_subset_1(esk1_0,esk2_0),esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.19/0.40  fof(c_0_11, plain, ![X7, X8]:(~m1_subset_1(X8,k1_zfmisc_1(X7))|k3_subset_1(X7,X8)=k4_xboole_0(X7,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.19/0.40  fof(c_0_12, plain, ![X11, X12, X13]:(~m1_subset_1(X12,k1_zfmisc_1(X11))|~m1_subset_1(X13,k1_zfmisc_1(X11))|m1_subset_1(k4_subset_1(X11,X12,X13),k1_zfmisc_1(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).
% 0.19/0.40  cnf(c_0_13, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.40  fof(c_0_15, plain, ![X9, X10]:(~m1_subset_1(X10,k1_zfmisc_1(X9))|m1_subset_1(k3_subset_1(X9,X10),k1_zfmisc_1(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.19/0.40  fof(c_0_16, plain, ![X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(X14))|k3_subset_1(X14,k3_subset_1(X14,X15))=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.19/0.40  cnf(c_0_17, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_18, plain, (m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  cnf(c_0_19, negated_conjecture, (k2_xboole_0(X1,esk3_0)=k4_subset_1(esk1_0,X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.40  cnf(c_0_20, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.40  cnf(c_0_21, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_22, plain, (k4_xboole_0(X1,k4_subset_1(X1,X2,X3))=k3_subset_1(X1,k4_subset_1(X1,X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.40  fof(c_0_23, plain, ![X4, X5, X6]:k4_xboole_0(k4_xboole_0(X4,X5),X6)=k4_xboole_0(X4,k2_xboole_0(X5,X6)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.19/0.40  cnf(c_0_24, negated_conjecture, (k2_xboole_0(k3_subset_1(esk1_0,X1),esk3_0)=k4_subset_1(esk1_0,k3_subset_1(esk1_0,X1),esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.40  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.40  fof(c_0_26, plain, ![X19, X20, X21]:(~m1_subset_1(X20,k1_zfmisc_1(X19))|k7_subset_1(X19,X20,X21)=k4_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.19/0.40  cnf(c_0_27, plain, (k3_subset_1(X1,k3_subset_1(X1,k4_subset_1(X1,X2,X3)))=k4_subset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_21, c_0_18])).
% 0.19/0.40  cnf(c_0_28, negated_conjecture, (k4_xboole_0(esk1_0,k4_subset_1(esk1_0,X1,esk3_0))=k3_subset_1(esk1_0,k4_subset_1(esk1_0,X1,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_22, c_0_14])).
% 0.19/0.40  cnf(c_0_29, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.40  cnf(c_0_30, negated_conjecture, (k2_xboole_0(k3_subset_1(esk1_0,esk2_0),esk3_0)=k4_subset_1(esk1_0,k3_subset_1(esk1_0,esk2_0),esk3_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.40  cnf(c_0_31, plain, (k4_xboole_0(X1,k3_subset_1(X1,X2))=k3_subset_1(X1,k3_subset_1(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_17, c_0_20])).
% 0.19/0.40  cnf(c_0_32, negated_conjecture, (k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk2_0))=esk2_0), inference(spm,[status(thm)],[c_0_21, c_0_25])).
% 0.19/0.40  cnf(c_0_33, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  cnf(c_0_34, negated_conjecture, (k3_subset_1(esk1_0,k3_subset_1(esk1_0,k4_subset_1(esk1_0,X1,esk3_0)))=k4_subset_1(esk1_0,X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_27, c_0_14])).
% 0.19/0.40  cnf(c_0_35, negated_conjecture, (k4_xboole_0(esk1_0,k4_subset_1(esk1_0,k3_subset_1(esk1_0,X1),esk3_0))=k3_subset_1(esk1_0,k4_subset_1(esk1_0,k3_subset_1(esk1_0,X1),esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_28, c_0_20])).
% 0.19/0.40  cnf(c_0_36, negated_conjecture, (k4_xboole_0(X1,k4_subset_1(esk1_0,k3_subset_1(esk1_0,esk2_0),esk3_0))=k4_xboole_0(k4_xboole_0(X1,k3_subset_1(esk1_0,esk2_0)),esk3_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.40  cnf(c_0_37, negated_conjecture, (k4_xboole_0(esk1_0,k3_subset_1(esk1_0,esk2_0))=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_25]), c_0_32])).
% 0.19/0.40  cnf(c_0_38, negated_conjecture, (k3_subset_1(esk1_0,k7_subset_1(esk1_0,esk2_0,esk3_0))!=k4_subset_1(esk1_0,k3_subset_1(esk1_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.40  cnf(c_0_39, negated_conjecture, (k7_subset_1(esk1_0,esk2_0,X1)=k4_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_33, c_0_25])).
% 0.19/0.40  cnf(c_0_40, negated_conjecture, (k3_subset_1(esk1_0,k3_subset_1(esk1_0,k4_subset_1(esk1_0,k3_subset_1(esk1_0,X1),esk3_0)))=k4_subset_1(esk1_0,k3_subset_1(esk1_0,X1),esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_34, c_0_20])).
% 0.19/0.40  cnf(c_0_41, negated_conjecture, (k3_subset_1(esk1_0,k4_subset_1(esk1_0,k3_subset_1(esk1_0,esk2_0),esk3_0))=k4_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_25]), c_0_36]), c_0_37])).
% 0.19/0.40  cnf(c_0_42, negated_conjecture, (k4_subset_1(esk1_0,k3_subset_1(esk1_0,esk2_0),esk3_0)!=k3_subset_1(esk1_0,k4_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.40  cnf(c_0_43, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_25]), c_0_41]), c_0_42]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 44
% 0.19/0.40  # Proof object clause steps            : 27
% 0.19/0.40  # Proof object formula steps           : 17
% 0.19/0.40  # Proof object conjectures             : 20
% 0.19/0.40  # Proof object clause conjectures      : 17
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 10
% 0.19/0.40  # Proof object initial formulas used   : 8
% 0.19/0.40  # Proof object generating inferences   : 16
% 0.19/0.40  # Proof object simplifying inferences  : 6
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 8
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 10
% 0.19/0.40  # Removed in clause preprocessing      : 0
% 0.19/0.40  # Initial clauses in saturation        : 10
% 0.19/0.40  # Processed clauses                    : 314
% 0.19/0.40  # ...of these trivial                  : 8
% 0.19/0.40  # ...subsumed                          : 23
% 0.19/0.40  # ...remaining for further processing  : 283
% 0.19/0.40  # Other redundant clauses eliminated   : 0
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 0
% 0.19/0.40  # Backward-rewritten                   : 47
% 0.19/0.40  # Generated clauses                    : 1117
% 0.19/0.40  # ...of the previous two non-trivial   : 1029
% 0.19/0.40  # Contextual simplify-reflections      : 0
% 0.19/0.40  # Paramodulations                      : 1117
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 0
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 226
% 0.19/0.40  #    Positive orientable unit clauses  : 107
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 1
% 0.19/0.40  #    Non-unit-clauses                  : 118
% 0.19/0.40  # Current number of unprocessed clauses: 733
% 0.19/0.40  # ...number of literals in the above   : 1797
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 57
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 1412
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 1412
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 23
% 0.19/0.40  # Unit Clause-clause subsumption calls : 301
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 148
% 0.19/0.40  # BW rewrite match successes           : 45
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 27584
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.056 s
% 0.19/0.40  # System time              : 0.004 s
% 0.19/0.40  # Total time               : 0.059 s
% 0.19/0.40  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
