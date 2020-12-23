%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:58 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 127 expanded)
%              Number of clauses        :   26 (  55 expanded)
%              Number of leaves         :    9 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   94 ( 306 expanded)
%              Number of equality atoms :   23 (  91 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t60_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( m1_setfam_1(X2,X1)
      <=> k5_setfam_1(X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(dt_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d12_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_setfam_1(X2,X1)
    <=> r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ( m1_setfam_1(X2,X1)
        <=> k5_setfam_1(X1,X2) = X1 ) ) ),
    inference(assume_negation,[status(cth)],[t60_setfam_1])).

fof(c_0_10,plain,(
    ! [X5,X6] :
      ( ~ r2_hidden(X5,X6)
      | r1_tarski(X5,k3_tarski(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

fof(c_0_11,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(X15,X16)
      | v1_xboole_0(X16)
      | r2_hidden(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_12,plain,(
    ! [X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13)))
      | k5_setfam_1(X13,X14) = k3_tarski(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

fof(c_0_13,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    & ( ~ m1_setfam_1(esk2_0,esk1_0)
      | k5_setfam_1(esk1_0,esk2_0) != esk1_0 )
    & ( m1_setfam_1(esk2_0,esk1_0)
      | k5_setfam_1(esk1_0,esk2_0) = esk1_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X7] : k3_tarski(k1_zfmisc_1(X7)) = X7 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

fof(c_0_17,plain,(
    ! [X8] : ~ v1_xboole_0(k1_zfmisc_1(X8)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_18,plain,(
    ! [X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X11)))
      | m1_subset_1(k5_setfam_1(X11,X12),k1_zfmisc_1(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).

cnf(c_0_19,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,plain,(
    ! [X3,X4] :
      ( ( r1_tarski(X3,X4)
        | X3 != X4 )
      & ( r1_tarski(X4,X3)
        | X3 != X4 )
      & ( ~ r1_tarski(X3,X4)
        | ~ r1_tarski(X4,X3)
        | X3 = X4 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_22,plain,(
    ! [X9,X10] :
      ( ( ~ m1_setfam_1(X10,X9)
        | r1_tarski(X9,k3_tarski(X10)) )
      & ( ~ r1_tarski(X9,k3_tarski(X10))
        | m1_setfam_1(X10,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).

cnf(c_0_23,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X2,k3_tarski(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_24,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( k5_setfam_1(esk1_0,esk2_0) = k3_tarski(esk2_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( r1_tarski(X2,k3_tarski(X1))
    | ~ m1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(k3_tarski(esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_20])])).

cnf(c_0_32,negated_conjecture,
    ( m1_setfam_1(esk2_0,esk1_0)
    | k5_setfam_1(esk1_0,esk2_0) = esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( ~ m1_setfam_1(esk2_0,esk1_0)
    | k5_setfam_1(esk1_0,esk2_0) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_35,plain,
    ( k3_tarski(X1) = X2
    | ~ m1_setfam_1(X1,X2)
    | ~ r1_tarski(k3_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k3_tarski(esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( k3_tarski(esk2_0) = esk1_0
    | m1_setfam_1(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_32,c_0_27])).

cnf(c_0_38,plain,
    ( m1_setfam_1(X2,X1)
    | ~ r1_tarski(X1,k3_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( k3_tarski(esk2_0) != esk1_0
    | ~ m1_setfam_1(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_34,c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( k3_tarski(esk2_0) = esk1_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_42,plain,
    ( m1_setfam_1(X1,k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( ~ m1_setfam_1(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41])])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_41]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:45:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.38  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.21/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.38  #
% 0.21/0.38  # Preprocessing time       : 0.027 s
% 0.21/0.38  
% 0.21/0.38  # Proof found!
% 0.21/0.38  # SZS status Theorem
% 0.21/0.38  # SZS output start CNFRefutation
% 0.21/0.38  fof(t60_setfam_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(m1_setfam_1(X2,X1)<=>k5_setfam_1(X1,X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_setfam_1)).
% 0.21/0.38  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.21/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.21/0.38  fof(redefinition_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k5_setfam_1(X1,X2)=k3_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 0.21/0.38  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.21/0.38  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.21/0.38  fof(dt_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 0.21/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.38  fof(d12_setfam_1, axiom, ![X1, X2]:(m1_setfam_1(X2,X1)<=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_setfam_1)).
% 0.21/0.38  fof(c_0_9, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(m1_setfam_1(X2,X1)<=>k5_setfam_1(X1,X2)=X1))), inference(assume_negation,[status(cth)],[t60_setfam_1])).
% 0.21/0.38  fof(c_0_10, plain, ![X5, X6]:(~r2_hidden(X5,X6)|r1_tarski(X5,k3_tarski(X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.21/0.38  fof(c_0_11, plain, ![X15, X16]:(~m1_subset_1(X15,X16)|(v1_xboole_0(X16)|r2_hidden(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.21/0.38  fof(c_0_12, plain, ![X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13)))|k5_setfam_1(X13,X14)=k3_tarski(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).
% 0.21/0.38  fof(c_0_13, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))&((~m1_setfam_1(esk2_0,esk1_0)|k5_setfam_1(esk1_0,esk2_0)!=esk1_0)&(m1_setfam_1(esk2_0,esk1_0)|k5_setfam_1(esk1_0,esk2_0)=esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.21/0.38  cnf(c_0_14, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.38  cnf(c_0_15, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.38  fof(c_0_16, plain, ![X7]:k3_tarski(k1_zfmisc_1(X7))=X7, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.21/0.38  fof(c_0_17, plain, ![X8]:~v1_xboole_0(k1_zfmisc_1(X8)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.21/0.38  fof(c_0_18, plain, ![X11, X12]:(~m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X11)))|m1_subset_1(k5_setfam_1(X11,X12),k1_zfmisc_1(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).
% 0.21/0.38  cnf(c_0_19, plain, (k5_setfam_1(X2,X1)=k3_tarski(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.38  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.38  fof(c_0_21, plain, ![X3, X4]:(((r1_tarski(X3,X4)|X3!=X4)&(r1_tarski(X4,X3)|X3!=X4))&(~r1_tarski(X3,X4)|~r1_tarski(X4,X3)|X3=X4)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.38  fof(c_0_22, plain, ![X9, X10]:((~m1_setfam_1(X10,X9)|r1_tarski(X9,k3_tarski(X10)))&(~r1_tarski(X9,k3_tarski(X10))|m1_setfam_1(X10,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).
% 0.21/0.38  cnf(c_0_23, plain, (v1_xboole_0(X1)|r1_tarski(X2,k3_tarski(X1))|~m1_subset_1(X2,X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.21/0.38  cnf(c_0_24, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.38  cnf(c_0_25, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.38  cnf(c_0_26, plain, (m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.38  cnf(c_0_27, negated_conjecture, (k5_setfam_1(esk1_0,esk2_0)=k3_tarski(esk2_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.21/0.38  cnf(c_0_28, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.38  cnf(c_0_29, plain, (r1_tarski(X2,k3_tarski(X1))|~m1_setfam_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.38  cnf(c_0_30, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.21/0.38  cnf(c_0_31, negated_conjecture, (m1_subset_1(k3_tarski(esk2_0),k1_zfmisc_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_20])])).
% 0.21/0.38  cnf(c_0_32, negated_conjecture, (m1_setfam_1(esk2_0,esk1_0)|k5_setfam_1(esk1_0,esk2_0)=esk1_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.38  cnf(c_0_33, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.38  cnf(c_0_34, negated_conjecture, (~m1_setfam_1(esk2_0,esk1_0)|k5_setfam_1(esk1_0,esk2_0)!=esk1_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.38  cnf(c_0_35, plain, (k3_tarski(X1)=X2|~m1_setfam_1(X1,X2)|~r1_tarski(k3_tarski(X1),X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.21/0.38  cnf(c_0_36, negated_conjecture, (r1_tarski(k3_tarski(esk2_0),esk1_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.21/0.38  cnf(c_0_37, negated_conjecture, (k3_tarski(esk2_0)=esk1_0|m1_setfam_1(esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_32, c_0_27])).
% 0.21/0.38  cnf(c_0_38, plain, (m1_setfam_1(X2,X1)|~r1_tarski(X1,k3_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.38  cnf(c_0_39, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_33])).
% 0.21/0.38  cnf(c_0_40, negated_conjecture, (k3_tarski(esk2_0)!=esk1_0|~m1_setfam_1(esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_34, c_0_27])).
% 0.21/0.38  cnf(c_0_41, negated_conjecture, (k3_tarski(esk2_0)=esk1_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.21/0.38  cnf(c_0_42, plain, (m1_setfam_1(X1,k3_tarski(X1))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.21/0.38  cnf(c_0_43, negated_conjecture, (~m1_setfam_1(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41])])).
% 0.21/0.38  cnf(c_0_44, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_41]), c_0_43]), ['proof']).
% 0.21/0.38  # SZS output end CNFRefutation
% 0.21/0.38  # Proof object total steps             : 45
% 0.21/0.38  # Proof object clause steps            : 26
% 0.21/0.38  # Proof object formula steps           : 19
% 0.21/0.38  # Proof object conjectures             : 14
% 0.21/0.38  # Proof object clause conjectures      : 11
% 0.21/0.38  # Proof object formula conjectures     : 3
% 0.21/0.38  # Proof object initial clauses used    : 13
% 0.21/0.38  # Proof object initial formulas used   : 9
% 0.21/0.38  # Proof object generating inferences   : 9
% 0.21/0.38  # Proof object simplifying inferences  : 10
% 0.21/0.38  # Training examples: 0 positive, 0 negative
% 0.21/0.38  # Parsed axioms                        : 9
% 0.21/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.38  # Initial clauses                      : 14
% 0.21/0.38  # Removed in clause preprocessing      : 0
% 0.21/0.38  # Initial clauses in saturation        : 14
% 0.21/0.38  # Processed clauses                    : 37
% 0.21/0.38  # ...of these trivial                  : 1
% 0.21/0.38  # ...subsumed                          : 0
% 0.21/0.38  # ...remaining for further processing  : 35
% 0.21/0.38  # Other redundant clauses eliminated   : 2
% 0.21/0.38  # Clauses deleted for lack of memory   : 0
% 0.21/0.38  # Backward-subsumed                    : 0
% 0.21/0.38  # Backward-rewritten                   : 8
% 0.21/0.38  # Generated clauses                    : 44
% 0.21/0.38  # ...of the previous two non-trivial   : 41
% 0.21/0.38  # Contextual simplify-reflections      : 1
% 0.21/0.38  # Paramodulations                      : 42
% 0.21/0.38  # Factorizations                       : 0
% 0.21/0.38  # Equation resolutions                 : 2
% 0.21/0.38  # Propositional unsat checks           : 0
% 0.21/0.38  #    Propositional check models        : 0
% 0.21/0.38  #    Propositional check unsatisfiable : 0
% 0.21/0.38  #    Propositional clauses             : 0
% 0.21/0.38  #    Propositional clauses after purity: 0
% 0.21/0.38  #    Propositional unsat core size     : 0
% 0.21/0.38  #    Propositional preprocessing time  : 0.000
% 0.21/0.38  #    Propositional encoding time       : 0.000
% 0.21/0.38  #    Propositional solver time         : 0.000
% 0.21/0.38  #    Success case prop preproc time    : 0.000
% 0.21/0.38  #    Success case prop encoding time   : 0.000
% 0.21/0.38  #    Success case prop solver time     : 0.000
% 0.21/0.38  # Current number of processed clauses  : 25
% 0.21/0.38  #    Positive orientable unit clauses  : 8
% 0.21/0.38  #    Positive unorientable unit clauses: 0
% 0.21/0.38  #    Negative unit clauses             : 2
% 0.21/0.38  #    Non-unit-clauses                  : 15
% 0.21/0.38  # Current number of unprocessed clauses: 18
% 0.21/0.38  # ...number of literals in the above   : 49
% 0.21/0.38  # Current number of archived formulas  : 0
% 0.21/0.38  # Current number of archived clauses   : 8
% 0.21/0.38  # Clause-clause subsumption calls (NU) : 14
% 0.21/0.38  # Rec. Clause-clause subsumption calls : 11
% 0.21/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.21/0.38  # Unit Clause-clause subsumption calls : 2
% 0.21/0.38  # Rewrite failures with RHS unbound    : 0
% 0.21/0.38  # BW rewrite match attempts            : 3
% 0.21/0.38  # BW rewrite match successes           : 2
% 0.21/0.38  # Condensation attempts                : 0
% 0.21/0.38  # Condensation successes               : 0
% 0.21/0.38  # Termbank termtop insertions          : 1204
% 0.21/0.38  
% 0.21/0.38  # -------------------------------------------------
% 0.21/0.38  # User time                : 0.028 s
% 0.21/0.38  # System time              : 0.003 s
% 0.21/0.38  # Total time               : 0.032 s
% 0.21/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
