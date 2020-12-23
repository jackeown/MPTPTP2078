%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:47 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   32 (  97 expanded)
%              Number of clauses        :   19 (  42 expanded)
%              Number of leaves         :    6 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 ( 132 expanded)
%              Number of equality atoms :   24 (  86 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t26_wellord1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k2_wellord1(k2_wellord1(X3,X1),X2) = k2_wellord1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).

fof(d6_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(c_0_6,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X14)
      | v1_relat_1(k3_xboole_0(X14,X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

fof(c_0_7,plain,(
    ! [X12,X13] : k1_setfam_1(k2_tarski(X12,X13)) = k3_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => k2_wellord1(k2_wellord1(X3,X1),X2) = k2_wellord1(X3,k3_xboole_0(X1,X2)) ) ),
    inference(assume_negation,[status(cth)],[t26_wellord1])).

fof(c_0_9,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X16)
      | k2_wellord1(X16,X17) = k3_xboole_0(X16,k2_zfmisc_1(X17,X17)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_wellord1])])])).

cnf(c_0_10,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & k2_wellord1(k2_wellord1(esk3_0,esk1_0),esk2_0) != k2_wellord1(esk3_0,k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_13,plain,
    ( k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X5,X6,X7] : k3_xboole_0(k3_xboole_0(X5,X6),X7) = k3_xboole_0(X5,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

fof(c_0_15,plain,(
    ! [X8,X9,X10,X11] : k2_zfmisc_1(k3_xboole_0(X8,X9),k3_xboole_0(X10,X11)) = k3_xboole_0(k2_zfmisc_1(X8,X10),k2_zfmisc_1(X9,X11)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

cnf(c_0_16,plain,
    ( v1_relat_1(k1_setfam_1(k2_tarski(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k2_wellord1(X1,X2) = k1_setfam_1(k2_tarski(X1,k2_zfmisc_1(X2,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_13,c_0_11])).

cnf(c_0_19,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(k1_setfam_1(k2_tarski(esk3_0,X1))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk3_0,k2_zfmisc_1(X1,X1))) = k2_wellord1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_23,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X1,X2)),X3)) = k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_11]),c_0_11]),c_0_11]),c_0_11])).

cnf(c_0_24,plain,
    ( k2_zfmisc_1(k1_setfam_1(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,X4))) = k1_setfam_1(k2_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_11]),c_0_11]),c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(k2_wellord1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( k2_wellord1(k2_wellord1(esk3_0,esk1_0),esk2_0) != k2_wellord1(esk3_0,k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X1,k2_zfmisc_1(X2,X3))),k2_zfmisc_1(X4,X5))) = k1_setfam_1(k2_tarski(X1,k2_zfmisc_1(k1_setfam_1(k2_tarski(X2,X4)),k1_setfam_1(k2_tarski(X3,X5))))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( k1_setfam_1(k2_tarski(k2_wellord1(esk3_0,X1),k2_zfmisc_1(X2,X2))) = k2_wellord1(k2_wellord1(esk3_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( k2_wellord1(k2_wellord1(esk3_0,esk1_0),esk2_0) != k2_wellord1(esk3_0,k1_setfam_1(k2_tarski(esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( k2_wellord1(k2_wellord1(esk3_0,X1),X2) = k2_wellord1(esk3_0,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_27]),c_0_22]),c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:06:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___208_B01_00_F1_SE_CS_SP_PS_S064A
% 0.20/0.40  # and selection function SelectComplexG.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.026 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 0.20/0.40  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.40  fof(t26_wellord1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>k2_wellord1(k2_wellord1(X3,X1),X2)=k2_wellord1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_wellord1)).
% 0.20/0.40  fof(d6_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k2_wellord1(X1,X2)=k3_xboole_0(X1,k2_zfmisc_1(X2,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_wellord1)).
% 0.20/0.40  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.20/0.40  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 0.20/0.40  fof(c_0_6, plain, ![X14, X15]:(~v1_relat_1(X14)|v1_relat_1(k3_xboole_0(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 0.20/0.40  fof(c_0_7, plain, ![X12, X13]:k1_setfam_1(k2_tarski(X12,X13))=k3_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.40  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>k2_wellord1(k2_wellord1(X3,X1),X2)=k2_wellord1(X3,k3_xboole_0(X1,X2)))), inference(assume_negation,[status(cth)],[t26_wellord1])).
% 0.20/0.40  fof(c_0_9, plain, ![X16, X17]:(~v1_relat_1(X16)|k2_wellord1(X16,X17)=k3_xboole_0(X16,k2_zfmisc_1(X17,X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_wellord1])])])).
% 0.20/0.40  cnf(c_0_10, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.40  cnf(c_0_11, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.40  fof(c_0_12, negated_conjecture, (v1_relat_1(esk3_0)&k2_wellord1(k2_wellord1(esk3_0,esk1_0),esk2_0)!=k2_wellord1(esk3_0,k3_xboole_0(esk1_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.20/0.40  cnf(c_0_13, plain, (k2_wellord1(X1,X2)=k3_xboole_0(X1,k2_zfmisc_1(X2,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  fof(c_0_14, plain, ![X5, X6, X7]:k3_xboole_0(k3_xboole_0(X5,X6),X7)=k3_xboole_0(X5,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.20/0.40  fof(c_0_15, plain, ![X8, X9, X10, X11]:k2_zfmisc_1(k3_xboole_0(X8,X9),k3_xboole_0(X10,X11))=k3_xboole_0(k2_zfmisc_1(X8,X10),k2_zfmisc_1(X9,X11)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 0.20/0.40  cnf(c_0_16, plain, (v1_relat_1(k1_setfam_1(k2_tarski(X1,X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.20/0.40  cnf(c_0_17, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  cnf(c_0_18, plain, (k2_wellord1(X1,X2)=k1_setfam_1(k2_tarski(X1,k2_zfmisc_1(X2,X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_13, c_0_11])).
% 0.20/0.40  cnf(c_0_19, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.40  cnf(c_0_20, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  cnf(c_0_21, negated_conjecture, (v1_relat_1(k1_setfam_1(k2_tarski(esk3_0,X1)))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.40  cnf(c_0_22, negated_conjecture, (k1_setfam_1(k2_tarski(esk3_0,k2_zfmisc_1(X1,X1)))=k2_wellord1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_18, c_0_17])).
% 0.20/0.40  cnf(c_0_23, plain, (k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X1,X2)),X3))=k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_11]), c_0_11]), c_0_11]), c_0_11])).
% 0.20/0.40  cnf(c_0_24, plain, (k2_zfmisc_1(k1_setfam_1(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,X4)))=k1_setfam_1(k2_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_11]), c_0_11]), c_0_11])).
% 0.20/0.40  cnf(c_0_25, negated_conjecture, (v1_relat_1(k2_wellord1(esk3_0,X1))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.40  cnf(c_0_26, negated_conjecture, (k2_wellord1(k2_wellord1(esk3_0,esk1_0),esk2_0)!=k2_wellord1(esk3_0,k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  cnf(c_0_27, plain, (k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X1,k2_zfmisc_1(X2,X3))),k2_zfmisc_1(X4,X5)))=k1_setfam_1(k2_tarski(X1,k2_zfmisc_1(k1_setfam_1(k2_tarski(X2,X4)),k1_setfam_1(k2_tarski(X3,X5)))))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.40  cnf(c_0_28, negated_conjecture, (k1_setfam_1(k2_tarski(k2_wellord1(esk3_0,X1),k2_zfmisc_1(X2,X2)))=k2_wellord1(k2_wellord1(esk3_0,X1),X2)), inference(spm,[status(thm)],[c_0_18, c_0_25])).
% 0.20/0.40  cnf(c_0_29, negated_conjecture, (k2_wellord1(k2_wellord1(esk3_0,esk1_0),esk2_0)!=k2_wellord1(esk3_0,k1_setfam_1(k2_tarski(esk1_0,esk2_0)))), inference(rw,[status(thm)],[c_0_26, c_0_11])).
% 0.20/0.40  cnf(c_0_30, negated_conjecture, (k2_wellord1(k2_wellord1(esk3_0,X1),X2)=k2_wellord1(esk3_0,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_27]), c_0_22]), c_0_28])).
% 0.20/0.40  cnf(c_0_31, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30])]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 32
% 0.20/0.40  # Proof object clause steps            : 19
% 0.20/0.40  # Proof object formula steps           : 13
% 0.20/0.40  # Proof object conjectures             : 12
% 0.20/0.40  # Proof object clause conjectures      : 9
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 7
% 0.20/0.40  # Proof object initial formulas used   : 6
% 0.20/0.40  # Proof object generating inferences   : 6
% 0.20/0.40  # Proof object simplifying inferences  : 14
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 6
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 7
% 0.20/0.40  # Removed in clause preprocessing      : 1
% 0.20/0.40  # Initial clauses in saturation        : 6
% 0.20/0.40  # Processed clauses                    : 95
% 0.20/0.40  # ...of these trivial                  : 27
% 0.20/0.40  # ...subsumed                          : 1
% 0.20/0.40  # ...remaining for further processing  : 67
% 0.20/0.40  # Other redundant clauses eliminated   : 0
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 0
% 0.20/0.40  # Backward-rewritten                   : 1
% 0.20/0.40  # Generated clauses                    : 1365
% 0.20/0.40  # ...of the previous two non-trivial   : 1078
% 0.20/0.40  # Contextual simplify-reflections      : 0
% 0.20/0.40  # Paramodulations                      : 1365
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 0
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
% 0.20/0.40  # Current number of processed clauses  : 60
% 0.20/0.40  #    Positive orientable unit clauses  : 50
% 0.20/0.40  #    Positive unorientable unit clauses: 8
% 0.20/0.40  #    Negative unit clauses             : 0
% 0.20/0.40  #    Non-unit-clauses                  : 2
% 0.20/0.40  # Current number of unprocessed clauses: 995
% 0.20/0.40  # ...number of literals in the above   : 995
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 8
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 0
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 0
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.40  # Unit Clause-clause subsumption calls : 17
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 355
% 0.20/0.40  # BW rewrite match successes           : 13
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 22092
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.049 s
% 0.20/0.40  # System time              : 0.003 s
% 0.20/0.40  # Total time               : 0.052 s
% 0.20/0.40  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
