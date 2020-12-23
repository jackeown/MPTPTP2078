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
% DateTime   : Thu Dec  3 10:48:03 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 (  48 expanded)
%              Number of clauses        :   19 (  22 expanded)
%              Number of leaves         :   10 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 (  62 expanded)
%              Number of equality atoms :   25 (  34 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t83_zfmisc_1,axiom,(
    ! [X1,X2] : k1_zfmisc_1(k3_xboole_0(X1,X2)) = k3_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_zfmisc_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t38_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k4_xboole_0(X2,X1))
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(t61_setfam_1,conjecture,(
    ! [X1] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_setfam_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t1_zfmisc_1,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_10,plain,(
    ! [X13,X14] : k1_zfmisc_1(k3_xboole_0(X13,X14)) = k3_xboole_0(k1_zfmisc_1(X13),k1_zfmisc_1(X14)) ),
    inference(variable_rename,[status(thm)],[t83_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X9,X10] : k4_xboole_0(X9,k4_xboole_0(X9,X10)) = k3_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_12,plain,(
    ! [X7,X8] :
      ( ~ r1_tarski(X7,k4_xboole_0(X8,X7))
      | X7 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).

cnf(c_0_13,plain,
    ( k1_zfmisc_1(k3_xboole_0(X1,X2)) = k3_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(assume_negation,[status(cth)],[t61_setfam_1])).

cnf(c_0_16,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k1_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k1_zfmisc_1(X1),k4_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_14])).

fof(c_0_18,plain,(
    ! [X11] : k4_xboole_0(k1_xboole_0,X11) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_19,plain,(
    ! [X5,X6] : r1_tarski(k4_xboole_0(X5,X6),X5) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_20,negated_conjecture,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_21,plain,(
    ! [X12] : k2_tarski(X12,X12) = k1_tarski(X12) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_22,plain,(
    ! [X3,X4] :
      ( ( k4_xboole_0(X3,X4) != k1_xboole_0
        | r1_tarski(X3,X4) )
      & ( ~ r1_tarski(X3,X4)
        | k4_xboole_0(X3,X4) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_23,plain,
    ( k4_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) = k1_xboole_0
    | ~ r1_tarski(k4_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)),k1_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[t1_zfmisc_1])).

fof(c_0_29,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X15,k1_zfmisc_1(X16))
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | m1_subset_1(X15,k1_zfmisc_1(X16)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X1)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_24]),c_0_25])])).

cnf(c_0_32,negated_conjecture,
    ( ~ m1_subset_1(k2_tarski(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k2_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:46:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.37  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.21/0.37  # and selection function SelectDiffNegLit.
% 0.21/0.37  #
% 0.21/0.37  # Preprocessing time       : 0.026 s
% 0.21/0.37  # Presaturation interreduction done
% 0.21/0.37  
% 0.21/0.37  # Proof found!
% 0.21/0.37  # SZS status Theorem
% 0.21/0.37  # SZS output start CNFRefutation
% 0.21/0.37  fof(t83_zfmisc_1, axiom, ![X1, X2]:k1_zfmisc_1(k3_xboole_0(X1,X2))=k3_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_zfmisc_1)).
% 0.21/0.37  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.21/0.37  fof(t38_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,k4_xboole_0(X2,X1))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 0.21/0.37  fof(t61_setfam_1, conjecture, ![X1]:m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_setfam_1)).
% 0.21/0.37  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.21/0.37  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.21/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.37  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.21/0.37  fof(t1_zfmisc_1, axiom, k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 0.21/0.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.37  fof(c_0_10, plain, ![X13, X14]:k1_zfmisc_1(k3_xboole_0(X13,X14))=k3_xboole_0(k1_zfmisc_1(X13),k1_zfmisc_1(X14)), inference(variable_rename,[status(thm)],[t83_zfmisc_1])).
% 0.21/0.37  fof(c_0_11, plain, ![X9, X10]:k4_xboole_0(X9,k4_xboole_0(X9,X10))=k3_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.21/0.37  fof(c_0_12, plain, ![X7, X8]:(~r1_tarski(X7,k4_xboole_0(X8,X7))|X7=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).
% 0.21/0.37  cnf(c_0_13, plain, (k1_zfmisc_1(k3_xboole_0(X1,X2))=k3_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.37  cnf(c_0_14, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.37  fof(c_0_15, negated_conjecture, ~(![X1]:m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(assume_negation,[status(cth)],[t61_setfam_1])).
% 0.21/0.37  cnf(c_0_16, plain, (X1=k1_xboole_0|~r1_tarski(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.37  cnf(c_0_17, plain, (k1_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(k1_zfmisc_1(X1),k4_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14]), c_0_14])).
% 0.21/0.37  fof(c_0_18, plain, ![X11]:k4_xboole_0(k1_xboole_0,X11)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.21/0.37  fof(c_0_19, plain, ![X5, X6]:r1_tarski(k4_xboole_0(X5,X6),X5), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.21/0.37  fof(c_0_20, negated_conjecture, ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.21/0.37  fof(c_0_21, plain, ![X12]:k2_tarski(X12,X12)=k1_tarski(X12), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.37  fof(c_0_22, plain, ![X3, X4]:((k4_xboole_0(X3,X4)!=k1_xboole_0|r1_tarski(X3,X4))&(~r1_tarski(X3,X4)|k4_xboole_0(X3,X4)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.21/0.37  cnf(c_0_23, plain, (k4_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2))=k1_xboole_0|~r1_tarski(k4_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)),k1_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.21/0.37  cnf(c_0_24, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.37  cnf(c_0_25, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.37  cnf(c_0_26, negated_conjecture, (~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.37  cnf(c_0_27, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.37  cnf(c_0_28, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(split_conjunct,[status(thm)],[t1_zfmisc_1])).
% 0.21/0.37  fof(c_0_29, plain, ![X15, X16]:((~m1_subset_1(X15,k1_zfmisc_1(X16))|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|m1_subset_1(X15,k1_zfmisc_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.37  cnf(c_0_30, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.37  cnf(c_0_31, plain, (k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X1))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_24]), c_0_25])])).
% 0.21/0.37  cnf(c_0_32, negated_conjecture, (~m1_subset_1(k2_tarski(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.21/0.37  cnf(c_0_33, plain, (k1_zfmisc_1(k1_xboole_0)=k2_tarski(k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_28, c_0_27])).
% 0.21/0.37  cnf(c_0_34, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.37  cnf(c_0_35, plain, (r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.21/0.37  cnf(c_0_36, negated_conjecture, (~m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.21/0.37  cnf(c_0_37, plain, (m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.21/0.37  cnf(c_0_38, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37])]), ['proof']).
% 0.21/0.37  # SZS output end CNFRefutation
% 0.21/0.37  # Proof object total steps             : 39
% 0.21/0.37  # Proof object clause steps            : 19
% 0.21/0.37  # Proof object formula steps           : 20
% 0.21/0.37  # Proof object conjectures             : 7
% 0.21/0.37  # Proof object clause conjectures      : 4
% 0.21/0.37  # Proof object formula conjectures     : 3
% 0.21/0.37  # Proof object initial clauses used    : 10
% 0.21/0.37  # Proof object initial formulas used   : 10
% 0.21/0.37  # Proof object generating inferences   : 4
% 0.21/0.37  # Proof object simplifying inferences  : 10
% 0.21/0.37  # Training examples: 0 positive, 0 negative
% 0.21/0.37  # Parsed axioms                        : 10
% 0.21/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.37  # Initial clauses                      : 12
% 0.21/0.37  # Removed in clause preprocessing      : 2
% 0.21/0.37  # Initial clauses in saturation        : 10
% 0.21/0.37  # Processed clauses                    : 46
% 0.21/0.37  # ...of these trivial                  : 2
% 0.21/0.37  # ...subsumed                          : 5
% 0.21/0.37  # ...remaining for further processing  : 39
% 0.21/0.37  # Other redundant clauses eliminated   : 0
% 0.21/0.37  # Clauses deleted for lack of memory   : 0
% 0.21/0.37  # Backward-subsumed                    : 0
% 0.21/0.37  # Backward-rewritten                   : 7
% 0.21/0.37  # Generated clauses                    : 74
% 0.21/0.37  # ...of the previous two non-trivial   : 50
% 0.21/0.37  # Contextual simplify-reflections      : 0
% 0.21/0.37  # Paramodulations                      : 74
% 0.21/0.37  # Factorizations                       : 0
% 0.21/0.37  # Equation resolutions                 : 0
% 0.21/0.37  # Propositional unsat checks           : 0
% 0.21/0.37  #    Propositional check models        : 0
% 0.21/0.37  #    Propositional check unsatisfiable : 0
% 0.21/0.37  #    Propositional clauses             : 0
% 0.21/0.37  #    Propositional clauses after purity: 0
% 0.21/0.37  #    Propositional unsat core size     : 0
% 0.21/0.37  #    Propositional preprocessing time  : 0.000
% 0.21/0.37  #    Propositional encoding time       : 0.000
% 0.21/0.37  #    Propositional solver time         : 0.000
% 0.21/0.37  #    Success case prop preproc time    : 0.000
% 0.21/0.37  #    Success case prop encoding time   : 0.000
% 0.21/0.37  #    Success case prop solver time     : 0.000
% 0.21/0.37  # Current number of processed clauses  : 22
% 0.21/0.37  #    Positive orientable unit clauses  : 13
% 0.21/0.37  #    Positive unorientable unit clauses: 0
% 0.21/0.37  #    Negative unit clauses             : 0
% 0.21/0.37  #    Non-unit-clauses                  : 9
% 0.21/0.37  # Current number of unprocessed clauses: 21
% 0.21/0.37  # ...number of literals in the above   : 31
% 0.21/0.37  # Current number of archived formulas  : 0
% 0.21/0.37  # Current number of archived clauses   : 19
% 0.21/0.37  # Clause-clause subsumption calls (NU) : 9
% 0.21/0.37  # Rec. Clause-clause subsumption calls : 9
% 0.21/0.37  # Non-unit clause-clause subsumptions  : 5
% 0.21/0.37  # Unit Clause-clause subsumption calls : 4
% 0.21/0.37  # Rewrite failures with RHS unbound    : 0
% 0.21/0.37  # BW rewrite match attempts            : 8
% 0.21/0.37  # BW rewrite match successes           : 7
% 0.21/0.37  # Condensation attempts                : 0
% 0.21/0.37  # Condensation successes               : 0
% 0.21/0.37  # Termbank termtop insertions          : 1454
% 0.21/0.37  
% 0.21/0.37  # -------------------------------------------------
% 0.21/0.37  # User time                : 0.028 s
% 0.21/0.37  # System time              : 0.004 s
% 0.21/0.37  # Total time               : 0.031 s
% 0.21/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
