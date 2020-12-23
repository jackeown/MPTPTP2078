%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:49 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   32 (  48 expanded)
%              Number of clauses        :   17 (  19 expanded)
%              Number of leaves         :    7 (  12 expanded)
%              Depth                    :    7
%              Number of atoms          :   63 ( 115 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t36_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(k3_subset_1(X1,X2),X3)
           => r1_tarski(k3_subset_1(X1,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_subset_1)).

fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(t31_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(c_0_7,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | k3_subset_1(X6,X7) = k4_xboole_0(X6,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_8,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k5_xboole_0(X4,k3_xboole_0(X4,X5)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r1_tarski(k3_subset_1(X1,X2),X3)
             => r1_tarski(k3_subset_1(X1,X3),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t36_subset_1])).

fof(c_0_10,plain,(
    ! [X8,X9] : m1_subset_1(k6_subset_1(X8,X9),k1_zfmisc_1(X8)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

fof(c_0_11,plain,(
    ! [X12,X13] : k6_subset_1(X12,X13) = k4_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_12,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_14,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
    & r1_tarski(k3_subset_1(esk1_0,esk2_0),esk3_0)
    & ~ r1_tarski(k3_subset_1(esk1_0,esk3_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_15,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | k3_subset_1(X10,k3_subset_1(X10,X11)) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_20,plain,(
    ! [X14,X15,X16] :
      ( ( ~ r1_tarski(X15,X16)
        | r1_tarski(k3_subset_1(X14,X16),k3_subset_1(X14,X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(X14)) )
      & ( ~ r1_tarski(k3_subset_1(X14,X16),k3_subset_1(X14,X15))
        | r1_tarski(X15,X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(X14)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_subset_1])])])])).

cnf(c_0_21,plain,
    ( m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)) = k3_subset_1(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( r1_tarski(X3,X2)
    | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk1_0,esk3_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk3_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk1_0,esk3_0),X1)
    | ~ r1_tarski(k3_subset_1(esk1_0,X1),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk1_0,esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])]),c_0_30]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:42:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S4c
% 0.14/0.39  # and selection function SelectCQPrecWNTNp.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.039 s
% 0.14/0.39  # Presaturation interreduction done
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.14/0.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.14/0.39  fof(t36_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(k3_subset_1(X1,X2),X3)=>r1_tarski(k3_subset_1(X1,X3),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_subset_1)).
% 0.14/0.39  fof(dt_k6_subset_1, axiom, ![X1, X2]:m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 0.14/0.39  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.14/0.39  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.14/0.39  fof(t31_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 0.14/0.39  fof(c_0_7, plain, ![X6, X7]:(~m1_subset_1(X7,k1_zfmisc_1(X6))|k3_subset_1(X6,X7)=k4_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.14/0.39  fof(c_0_8, plain, ![X4, X5]:k4_xboole_0(X4,X5)=k5_xboole_0(X4,k3_xboole_0(X4,X5)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.14/0.39  fof(c_0_9, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(k3_subset_1(X1,X2),X3)=>r1_tarski(k3_subset_1(X1,X3),X2))))), inference(assume_negation,[status(cth)],[t36_subset_1])).
% 0.14/0.39  fof(c_0_10, plain, ![X8, X9]:m1_subset_1(k6_subset_1(X8,X9),k1_zfmisc_1(X8)), inference(variable_rename,[status(thm)],[dt_k6_subset_1])).
% 0.14/0.39  fof(c_0_11, plain, ![X12, X13]:k6_subset_1(X12,X13)=k4_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.14/0.39  cnf(c_0_12, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.39  cnf(c_0_13, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.39  fof(c_0_14, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))&(r1_tarski(k3_subset_1(esk1_0,esk2_0),esk3_0)&~r1_tarski(k3_subset_1(esk1_0,esk3_0),esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.14/0.39  cnf(c_0_15, plain, (m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_16, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_17, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.14/0.39  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.39  fof(c_0_19, plain, ![X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(X10))|k3_subset_1(X10,k3_subset_1(X10,X11))=X11), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.14/0.39  fof(c_0_20, plain, ![X14, X15, X16]:((~r1_tarski(X15,X16)|r1_tarski(k3_subset_1(X14,X16),k3_subset_1(X14,X15))|~m1_subset_1(X16,k1_zfmisc_1(X14))|~m1_subset_1(X15,k1_zfmisc_1(X14)))&(~r1_tarski(k3_subset_1(X14,X16),k3_subset_1(X14,X15))|r1_tarski(X15,X16)|~m1_subset_1(X16,k1_zfmisc_1(X14))|~m1_subset_1(X15,k1_zfmisc_1(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_subset_1])])])])).
% 0.14/0.39  cnf(c_0_21, plain, (m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_13])).
% 0.14/0.39  cnf(c_0_22, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0))=k3_subset_1(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.14/0.39  cnf(c_0_23, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.39  cnf(c_0_24, plain, (r1_tarski(X3,X2)|~r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.39  cnf(c_0_25, negated_conjecture, (m1_subset_1(k3_subset_1(esk1_0,esk3_0),k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.14/0.39  cnf(c_0_26, negated_conjecture, (k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk3_0))=esk3_0), inference(spm,[status(thm)],[c_0_23, c_0_18])).
% 0.14/0.39  cnf(c_0_27, negated_conjecture, (r1_tarski(k3_subset_1(esk1_0,esk3_0),X1)|~r1_tarski(k3_subset_1(esk1_0,X1),esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(esk1_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.14/0.39  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.39  cnf(c_0_29, negated_conjecture, (r1_tarski(k3_subset_1(esk1_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.39  cnf(c_0_30, negated_conjecture, (~r1_tarski(k3_subset_1(esk1_0,esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.39  cnf(c_0_31, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])]), c_0_30]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 32
% 0.14/0.39  # Proof object clause steps            : 17
% 0.14/0.39  # Proof object formula steps           : 15
% 0.14/0.39  # Proof object conjectures             : 12
% 0.14/0.39  # Proof object clause conjectures      : 9
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 10
% 0.14/0.39  # Proof object initial formulas used   : 7
% 0.14/0.39  # Proof object generating inferences   : 5
% 0.14/0.39  # Proof object simplifying inferences  : 7
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 7
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 11
% 0.14/0.39  # Removed in clause preprocessing      : 2
% 0.14/0.39  # Initial clauses in saturation        : 9
% 0.14/0.39  # Processed clauses                    : 41
% 0.14/0.39  # ...of these trivial                  : 0
% 0.14/0.39  # ...subsumed                          : 3
% 0.14/0.39  # ...remaining for further processing  : 38
% 0.14/0.39  # Other redundant clauses eliminated   : 0
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 0
% 0.14/0.39  # Backward-rewritten                   : 0
% 0.14/0.39  # Generated clauses                    : 55
% 0.14/0.39  # ...of the previous two non-trivial   : 35
% 0.14/0.39  # Contextual simplify-reflections      : 0
% 0.14/0.39  # Paramodulations                      : 55
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 0
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 29
% 0.14/0.39  #    Positive orientable unit clauses  : 14
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 1
% 0.14/0.39  #    Non-unit-clauses                  : 14
% 0.14/0.39  # Current number of unprocessed clauses: 12
% 0.14/0.39  # ...number of literals in the above   : 27
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 11
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 24
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 22
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 3
% 0.14/0.39  # Unit Clause-clause subsumption calls : 0
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 1
% 0.14/0.39  # BW rewrite match successes           : 0
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 1596
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.038 s
% 0.14/0.39  # System time              : 0.006 s
% 0.14/0.39  # Total time               : 0.044 s
% 0.14/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
