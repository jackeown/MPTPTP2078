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
% DateTime   : Thu Dec  3 10:46:23 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   31 (  52 expanded)
%              Number of clauses        :   18 (  22 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 ( 108 expanded)
%              Number of equality atoms :   14 (  17 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t41_subset_1])).

fof(c_0_7,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | ~ m1_subset_1(X13,k1_zfmisc_1(X11))
      | m1_subset_1(k4_subset_1(X11,X12,X13),k1_zfmisc_1(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

fof(c_0_8,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
    & ~ r1_tarski(k3_subset_1(esk1_0,k4_subset_1(esk1_0,esk2_0,esk3_0)),k3_subset_1(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X9,X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | k3_subset_1(X9,X10) = k4_xboole_0(X9,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_10,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | ~ m1_subset_1(X16,k1_zfmisc_1(X14))
      | k4_subset_1(X14,X15,X16) = k2_xboole_0(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_13,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(k4_subset_1(esk1_0,X1,esk3_0),k1_zfmisc_1(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk1_0,k4_subset_1(esk1_0,esk2_0,esk3_0)),k3_subset_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( k3_subset_1(esk1_0,esk2_0) = k4_xboole_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(k4_subset_1(esk1_0,esk2_0,esk3_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_14])).

fof(c_0_20,plain,(
    ! [X6,X7,X8] : k4_xboole_0(k4_xboole_0(X6,X7),X8) = k4_xboole_0(X6,k2_xboole_0(X7,X8)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_21,negated_conjecture,
    ( k2_xboole_0(X1,esk3_0) = k4_subset_1(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk1_0,k4_subset_1(esk1_0,esk2_0,esk3_0)),k4_xboole_0(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( k3_subset_1(esk1_0,k4_subset_1(esk1_0,esk2_0,esk3_0)) = k4_xboole_0(esk1_0,k4_subset_1(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_19])).

cnf(c_0_24,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk3_0) = k4_subset_1(esk1_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_14])).

fof(c_0_26,plain,(
    ! [X4,X5] : r1_tarski(k4_xboole_0(X4,X5),X4) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_27,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(esk1_0,k4_subset_1(esk1_0,esk2_0,esk3_0)),k4_xboole_0(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( k4_xboole_0(X1,k4_subset_1(esk1_0,esk2_0,esk3_0)) = k4_xboole_0(k4_xboole_0(X1,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:43:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S075I
% 0.18/0.36  # and selection function SelectCQAr.
% 0.18/0.36  #
% 0.18/0.36  # Preprocessing time       : 0.023 s
% 0.18/0.36  # Presaturation interreduction done
% 0.18/0.36  
% 0.18/0.36  # Proof found!
% 0.18/0.36  # SZS status Theorem
% 0.18/0.36  # SZS output start CNFRefutation
% 0.18/0.36  fof(t41_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_subset_1)).
% 0.18/0.36  fof(dt_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 0.18/0.36  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.18/0.36  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.18/0.36  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.18/0.36  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.18/0.36  fof(c_0_6, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2))))), inference(assume_negation,[status(cth)],[t41_subset_1])).
% 0.18/0.36  fof(c_0_7, plain, ![X11, X12, X13]:(~m1_subset_1(X12,k1_zfmisc_1(X11))|~m1_subset_1(X13,k1_zfmisc_1(X11))|m1_subset_1(k4_subset_1(X11,X12,X13),k1_zfmisc_1(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).
% 0.18/0.36  fof(c_0_8, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))&~r1_tarski(k3_subset_1(esk1_0,k4_subset_1(esk1_0,esk2_0,esk3_0)),k3_subset_1(esk1_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.18/0.36  fof(c_0_9, plain, ![X9, X10]:(~m1_subset_1(X10,k1_zfmisc_1(X9))|k3_subset_1(X9,X10)=k4_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.18/0.36  cnf(c_0_10, plain, (m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.36  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.36  fof(c_0_12, plain, ![X14, X15, X16]:(~m1_subset_1(X15,k1_zfmisc_1(X14))|~m1_subset_1(X16,k1_zfmisc_1(X14))|k4_subset_1(X14,X15,X16)=k2_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.18/0.36  cnf(c_0_13, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.36  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.36  cnf(c_0_15, negated_conjecture, (m1_subset_1(k4_subset_1(esk1_0,X1,esk3_0),k1_zfmisc_1(esk1_0))|~m1_subset_1(X1,k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.18/0.36  cnf(c_0_16, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.36  cnf(c_0_17, negated_conjecture, (~r1_tarski(k3_subset_1(esk1_0,k4_subset_1(esk1_0,esk2_0,esk3_0)),k3_subset_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.36  cnf(c_0_18, negated_conjecture, (k3_subset_1(esk1_0,esk2_0)=k4_xboole_0(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.18/0.36  cnf(c_0_19, negated_conjecture, (m1_subset_1(k4_subset_1(esk1_0,esk2_0,esk3_0),k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_15, c_0_14])).
% 0.18/0.36  fof(c_0_20, plain, ![X6, X7, X8]:k4_xboole_0(k4_xboole_0(X6,X7),X8)=k4_xboole_0(X6,k2_xboole_0(X7,X8)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.18/0.36  cnf(c_0_21, negated_conjecture, (k2_xboole_0(X1,esk3_0)=k4_subset_1(esk1_0,X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_16, c_0_11])).
% 0.18/0.36  cnf(c_0_22, negated_conjecture, (~r1_tarski(k3_subset_1(esk1_0,k4_subset_1(esk1_0,esk2_0,esk3_0)),k4_xboole_0(esk1_0,esk2_0))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.18/0.36  cnf(c_0_23, negated_conjecture, (k3_subset_1(esk1_0,k4_subset_1(esk1_0,esk2_0,esk3_0))=k4_xboole_0(esk1_0,k4_subset_1(esk1_0,esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_13, c_0_19])).
% 0.18/0.36  cnf(c_0_24, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.36  cnf(c_0_25, negated_conjecture, (k2_xboole_0(esk2_0,esk3_0)=k4_subset_1(esk1_0,esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_21, c_0_14])).
% 0.18/0.36  fof(c_0_26, plain, ![X4, X5]:r1_tarski(k4_xboole_0(X4,X5),X4), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.18/0.36  cnf(c_0_27, negated_conjecture, (~r1_tarski(k4_xboole_0(esk1_0,k4_subset_1(esk1_0,esk2_0,esk3_0)),k4_xboole_0(esk1_0,esk2_0))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.18/0.36  cnf(c_0_28, negated_conjecture, (k4_xboole_0(X1,k4_subset_1(esk1_0,esk2_0,esk3_0))=k4_xboole_0(k4_xboole_0(X1,esk2_0),esk3_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.18/0.36  cnf(c_0_29, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.36  cnf(c_0_30, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_29])]), ['proof']).
% 0.18/0.36  # SZS output end CNFRefutation
% 0.18/0.36  # Proof object total steps             : 31
% 0.18/0.36  # Proof object clause steps            : 18
% 0.18/0.36  # Proof object formula steps           : 13
% 0.18/0.36  # Proof object conjectures             : 16
% 0.18/0.36  # Proof object clause conjectures      : 13
% 0.18/0.36  # Proof object formula conjectures     : 3
% 0.18/0.36  # Proof object initial clauses used    : 8
% 0.18/0.36  # Proof object initial formulas used   : 6
% 0.18/0.36  # Proof object generating inferences   : 7
% 0.18/0.36  # Proof object simplifying inferences  : 5
% 0.18/0.36  # Training examples: 0 positive, 0 negative
% 0.18/0.36  # Parsed axioms                        : 6
% 0.18/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.36  # Initial clauses                      : 8
% 0.18/0.36  # Removed in clause preprocessing      : 0
% 0.18/0.36  # Initial clauses in saturation        : 8
% 0.18/0.36  # Processed clauses                    : 61
% 0.18/0.36  # ...of these trivial                  : 1
% 0.18/0.36  # ...subsumed                          : 0
% 0.18/0.36  # ...remaining for further processing  : 60
% 0.18/0.36  # Other redundant clauses eliminated   : 0
% 0.18/0.36  # Clauses deleted for lack of memory   : 0
% 0.18/0.36  # Backward-subsumed                    : 0
% 0.18/0.36  # Backward-rewritten                   : 5
% 0.18/0.36  # Generated clauses                    : 274
% 0.18/0.36  # ...of the previous two non-trivial   : 269
% 0.18/0.36  # Contextual simplify-reflections      : 0
% 0.18/0.36  # Paramodulations                      : 274
% 0.18/0.36  # Factorizations                       : 0
% 0.18/0.36  # Equation resolutions                 : 0
% 0.18/0.36  # Propositional unsat checks           : 0
% 0.18/0.36  #    Propositional check models        : 0
% 0.18/0.36  #    Propositional check unsatisfiable : 0
% 0.18/0.36  #    Propositional clauses             : 0
% 0.18/0.36  #    Propositional clauses after purity: 0
% 0.18/0.36  #    Propositional unsat core size     : 0
% 0.18/0.36  #    Propositional preprocessing time  : 0.000
% 0.18/0.36  #    Propositional encoding time       : 0.000
% 0.18/0.36  #    Propositional solver time         : 0.000
% 0.18/0.36  #    Success case prop preproc time    : 0.000
% 0.18/0.36  #    Success case prop encoding time   : 0.000
% 0.18/0.36  #    Success case prop solver time     : 0.000
% 0.18/0.36  # Current number of processed clauses  : 47
% 0.18/0.36  #    Positive orientable unit clauses  : 33
% 0.18/0.36  #    Positive unorientable unit clauses: 0
% 0.18/0.36  #    Negative unit clauses             : 0
% 0.18/0.36  #    Non-unit-clauses                  : 14
% 0.18/0.36  # Current number of unprocessed clauses: 223
% 0.18/0.36  # ...number of literals in the above   : 248
% 0.18/0.36  # Current number of archived formulas  : 0
% 0.18/0.36  # Current number of archived clauses   : 13
% 0.18/0.36  # Clause-clause subsumption calls (NU) : 25
% 0.18/0.36  # Rec. Clause-clause subsumption calls : 25
% 0.18/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.18/0.36  # Unit Clause-clause subsumption calls : 14
% 0.18/0.36  # Rewrite failures with RHS unbound    : 0
% 0.18/0.36  # BW rewrite match attempts            : 50
% 0.18/0.36  # BW rewrite match successes           : 4
% 0.18/0.36  # Condensation attempts                : 0
% 0.18/0.36  # Condensation successes               : 0
% 0.18/0.36  # Termbank termtop insertions          : 6002
% 0.18/0.36  
% 0.18/0.36  # -------------------------------------------------
% 0.18/0.36  # User time                : 0.028 s
% 0.18/0.36  # System time              : 0.002 s
% 0.18/0.36  # Total time               : 0.030 s
% 0.18/0.36  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
