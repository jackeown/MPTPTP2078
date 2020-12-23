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
% DateTime   : Thu Dec  3 10:47:38 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   37 (  70 expanded)
%              Number of clauses        :   19 (  31 expanded)
%              Number of leaves         :    9 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :   97 ( 157 expanded)
%              Number of equality atoms :   25 (  41 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t46_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ~ ( X2 != k1_xboole_0
          & k7_setfam_1(X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(involutiveness_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k7_setfam_1(X1,k7_setfam_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(c_0_9,plain,(
    ! [X22,X23] :
      ( ( ~ m1_subset_1(X22,k1_zfmisc_1(X23))
        | r1_tarski(X22,X23) )
      & ( ~ r1_tarski(X22,X23)
        | m1_subset_1(X22,k1_zfmisc_1(X23)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_10,plain,(
    ! [X11] : m1_subset_1(k2_subset_1(X11),k1_zfmisc_1(X11)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_11,plain,(
    ! [X27,X28,X29] :
      ( ~ r2_hidden(X27,X28)
      | ~ m1_subset_1(X28,k1_zfmisc_1(X29))
      | ~ v1_xboole_0(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_12,plain,(
    ! [X10] :
      ( ~ r1_tarski(X10,k1_xboole_0)
      | X10 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r1_tarski(k2_subset_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ~ ( X2 != k1_xboole_0
            & k7_setfam_1(X1,X2) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t46_setfam_1])).

fof(c_0_19,plain,(
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
      & ( m1_subset_1(esk2_3(X13,X14,X15),k1_zfmisc_1(X13))
        | X15 = k7_setfam_1(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))) )
      & ( ~ r2_hidden(esk2_3(X13,X14,X15),X15)
        | ~ r2_hidden(k3_subset_1(X13,esk2_3(X13,X14,X15)),X14)
        | X15 = k7_setfam_1(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))) )
      & ( r2_hidden(esk2_3(X13,X14,X15),X15)
        | r2_hidden(k3_subset_1(X13,esk2_3(X13,X14,X15)),X14)
        | X15 = k7_setfam_1(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).

fof(c_0_20,plain,(
    ! [X12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X12)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,k2_subset_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_14])).

cnf(c_0_22,plain,
    ( k2_subset_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_24,plain,(
    ! [X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X20)))
      | k7_setfam_1(X20,k7_setfam_1(X20,X21)) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).

fof(c_0_25,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    & esk4_0 != k1_xboole_0
    & k7_setfam_1(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_26,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(k3_subset_1(X1,esk2_3(X1,X2,X3)),X2)
    | X3 = k7_setfam_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_29,plain,
    ( k7_setfam_1(X2,k7_setfam_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k7_setfam_1(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k7_setfam_1(X1,X2) = k1_xboole_0
    | r2_hidden(k3_subset_1(X1,esk2_3(X1,X2,k1_xboole_0)),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( k7_setfam_1(esk3_0,k1_xboole_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_34,plain,
    ( k7_setfam_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_27]),c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n021.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 13:05:04 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.32  # No SInE strategy applied
% 0.11/0.32  # Trying AutoSched0 for 299 seconds
% 0.11/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S049N
% 0.11/0.36  # and selection function PSelectComplexPreferEQ.
% 0.11/0.36  #
% 0.11/0.36  # Preprocessing time       : 0.028 s
% 0.11/0.36  # Presaturation interreduction done
% 0.11/0.36  
% 0.11/0.36  # Proof found!
% 0.11/0.36  # SZS status Theorem
% 0.11/0.36  # SZS output start CNFRefutation
% 0.11/0.36  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.11/0.36  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.11/0.36  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.11/0.36  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.11/0.36  fof(t46_setfam_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>~((X2!=k1_xboole_0&k7_setfam_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_setfam_1)).
% 0.11/0.36  fof(d8_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X3=k7_setfam_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(r2_hidden(X4,X3)<=>r2_hidden(k3_subset_1(X1,X4),X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_setfam_1)).
% 0.11/0.36  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.11/0.36  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.11/0.36  fof(involutiveness_k7_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k7_setfam_1(X1,k7_setfam_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 0.11/0.36  fof(c_0_9, plain, ![X22, X23]:((~m1_subset_1(X22,k1_zfmisc_1(X23))|r1_tarski(X22,X23))&(~r1_tarski(X22,X23)|m1_subset_1(X22,k1_zfmisc_1(X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.11/0.36  fof(c_0_10, plain, ![X11]:m1_subset_1(k2_subset_1(X11),k1_zfmisc_1(X11)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.11/0.36  fof(c_0_11, plain, ![X27, X28, X29]:(~r2_hidden(X27,X28)|~m1_subset_1(X28,k1_zfmisc_1(X29))|~v1_xboole_0(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.11/0.36  fof(c_0_12, plain, ![X10]:(~r1_tarski(X10,k1_xboole_0)|X10=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.11/0.36  cnf(c_0_13, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.11/0.36  cnf(c_0_14, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.11/0.36  cnf(c_0_15, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.11/0.36  cnf(c_0_16, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.36  cnf(c_0_17, plain, (r1_tarski(k2_subset_1(X1),X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.11/0.36  fof(c_0_18, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>~((X2!=k1_xboole_0&k7_setfam_1(X1,X2)=k1_xboole_0)))), inference(assume_negation,[status(cth)],[t46_setfam_1])).
% 0.11/0.36  fof(c_0_19, plain, ![X13, X14, X15, X16]:(((~r2_hidden(X16,X15)|r2_hidden(k3_subset_1(X13,X16),X14)|~m1_subset_1(X16,k1_zfmisc_1(X13))|X15!=k7_setfam_1(X13,X14)|~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))|~m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))))&(~r2_hidden(k3_subset_1(X13,X16),X14)|r2_hidden(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(X13))|X15!=k7_setfam_1(X13,X14)|~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))|~m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13)))))&((m1_subset_1(esk2_3(X13,X14,X15),k1_zfmisc_1(X13))|X15=k7_setfam_1(X13,X14)|~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))|~m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))))&((~r2_hidden(esk2_3(X13,X14,X15),X15)|~r2_hidden(k3_subset_1(X13,esk2_3(X13,X14,X15)),X14)|X15=k7_setfam_1(X13,X14)|~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))|~m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))))&(r2_hidden(esk2_3(X13,X14,X15),X15)|r2_hidden(k3_subset_1(X13,esk2_3(X13,X14,X15)),X14)|X15=k7_setfam_1(X13,X14)|~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))|~m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).
% 0.11/0.36  fof(c_0_20, plain, ![X12]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X12)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.11/0.36  cnf(c_0_21, plain, (~r2_hidden(X1,k2_subset_1(X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_15, c_0_14])).
% 0.11/0.36  cnf(c_0_22, plain, (k2_subset_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.11/0.36  cnf(c_0_23, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.11/0.36  fof(c_0_24, plain, ![X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X20)))|k7_setfam_1(X20,k7_setfam_1(X20,X21))=X21), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).
% 0.11/0.36  fof(c_0_25, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))&(esk4_0!=k1_xboole_0&k7_setfam_1(esk3_0,esk4_0)=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.11/0.36  cnf(c_0_26, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(k3_subset_1(X1,esk2_3(X1,X2,X3)),X2)|X3=k7_setfam_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.11/0.36  cnf(c_0_27, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.11/0.36  cnf(c_0_28, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.11/0.36  cnf(c_0_29, plain, (k7_setfam_1(X2,k7_setfam_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.11/0.36  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.11/0.36  cnf(c_0_31, negated_conjecture, (k7_setfam_1(esk3_0,esk4_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.11/0.36  cnf(c_0_32, plain, (k7_setfam_1(X1,X2)=k1_xboole_0|r2_hidden(k3_subset_1(X1,esk2_3(X1,X2,k1_xboole_0)),X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.11/0.36  cnf(c_0_33, negated_conjecture, (k7_setfam_1(esk3_0,k1_xboole_0)=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.11/0.36  cnf(c_0_34, plain, (k7_setfam_1(X1,k1_xboole_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_27]), c_0_28])).
% 0.11/0.36  cnf(c_0_35, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.11/0.36  cnf(c_0_36, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_35]), ['proof']).
% 0.11/0.36  # SZS output end CNFRefutation
% 0.11/0.36  # Proof object total steps             : 37
% 0.11/0.36  # Proof object clause steps            : 19
% 0.11/0.36  # Proof object formula steps           : 18
% 0.11/0.36  # Proof object conjectures             : 8
% 0.11/0.36  # Proof object clause conjectures      : 5
% 0.11/0.36  # Proof object formula conjectures     : 3
% 0.11/0.36  # Proof object initial clauses used    : 11
% 0.11/0.36  # Proof object initial formulas used   : 9
% 0.11/0.36  # Proof object generating inferences   : 7
% 0.11/0.36  # Proof object simplifying inferences  : 7
% 0.11/0.36  # Training examples: 0 positive, 0 negative
% 0.11/0.36  # Parsed axioms                        : 13
% 0.11/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.36  # Initial clauses                      : 21
% 0.11/0.36  # Removed in clause preprocessing      : 0
% 0.11/0.36  # Initial clauses in saturation        : 21
% 0.11/0.36  # Processed clauses                    : 66
% 0.11/0.36  # ...of these trivial                  : 1
% 0.11/0.36  # ...subsumed                          : 1
% 0.11/0.36  # ...remaining for further processing  : 64
% 0.11/0.36  # Other redundant clauses eliminated   : 2
% 0.11/0.36  # Clauses deleted for lack of memory   : 0
% 0.11/0.36  # Backward-subsumed                    : 0
% 0.11/0.36  # Backward-rewritten                   : 6
% 0.11/0.36  # Generated clauses                    : 71
% 0.11/0.36  # ...of the previous two non-trivial   : 48
% 0.11/0.36  # Contextual simplify-reflections      : 3
% 0.11/0.36  # Paramodulations                      : 69
% 0.11/0.36  # Factorizations                       : 0
% 0.11/0.36  # Equation resolutions                 : 2
% 0.11/0.36  # Propositional unsat checks           : 0
% 0.11/0.36  #    Propositional check models        : 0
% 0.11/0.36  #    Propositional check unsatisfiable : 0
% 0.11/0.36  #    Propositional clauses             : 0
% 0.11/0.36  #    Propositional clauses after purity: 0
% 0.11/0.36  #    Propositional unsat core size     : 0
% 0.11/0.36  #    Propositional preprocessing time  : 0.000
% 0.11/0.36  #    Propositional encoding time       : 0.000
% 0.11/0.36  #    Propositional solver time         : 0.000
% 0.11/0.36  #    Success case prop preproc time    : 0.000
% 0.11/0.36  #    Success case prop encoding time   : 0.000
% 0.11/0.36  #    Success case prop solver time     : 0.000
% 0.11/0.36  # Current number of processed clauses  : 35
% 0.11/0.36  #    Positive orientable unit clauses  : 10
% 0.11/0.36  #    Positive unorientable unit clauses: 0
% 0.11/0.36  #    Negative unit clauses             : 2
% 0.11/0.36  #    Non-unit-clauses                  : 23
% 0.11/0.36  # Current number of unprocessed clauses: 23
% 0.11/0.36  # ...number of literals in the above   : 64
% 0.11/0.36  # Current number of archived formulas  : 0
% 0.11/0.36  # Current number of archived clauses   : 27
% 0.11/0.36  # Clause-clause subsumption calls (NU) : 179
% 0.11/0.36  # Rec. Clause-clause subsumption calls : 84
% 0.11/0.36  # Non-unit clause-clause subsumptions  : 4
% 0.11/0.36  # Unit Clause-clause subsumption calls : 9
% 0.11/0.36  # Rewrite failures with RHS unbound    : 0
% 0.11/0.36  # BW rewrite match attempts            : 3
% 0.11/0.36  # BW rewrite match successes           : 3
% 0.11/0.36  # Condensation attempts                : 0
% 0.11/0.36  # Condensation successes               : 0
% 0.11/0.36  # Termbank termtop insertions          : 2606
% 0.11/0.36  
% 0.11/0.36  # -------------------------------------------------
% 0.11/0.36  # User time                : 0.030 s
% 0.11/0.36  # System time              : 0.004 s
% 0.11/0.36  # Total time               : 0.034 s
% 0.11/0.36  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
