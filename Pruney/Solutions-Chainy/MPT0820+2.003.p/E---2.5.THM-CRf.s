%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:57:10 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   41 (  73 expanded)
%              Number of clauses        :   22 (  31 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :   85 ( 146 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t19_relset_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => r1_tarski(k3_relat_1(X3),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => r1_tarski(k3_relat_1(X3),k2_xboole_0(X1,X2)) ) ),
    inference(assume_negation,[status(cth)],[t19_relset_1])).

fof(c_0_10,plain,(
    ! [X20,X21,X22] :
      ( ( v4_relat_1(X22,X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( v5_relat_1(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_11,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & ~ r1_tarski(k3_relat_1(esk3_0),k2_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_12,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | v1_relat_1(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_13,plain,(
    ! [X14,X15] :
      ( ( ~ v5_relat_1(X15,X14)
        | r1_tarski(k2_relat_1(X15),X14)
        | ~ v1_relat_1(X15) )
      & ( ~ r1_tarski(k2_relat_1(X15),X14)
        | v5_relat_1(X15,X14)
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_14,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X12,X13] :
      ( ( ~ v4_relat_1(X13,X12)
        | r1_tarski(k1_relat_1(X13),X12)
        | ~ v1_relat_1(X13) )
      & ( ~ r1_tarski(k1_relat_1(X13),X12)
        | v4_relat_1(X13,X12)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_18,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_19,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | r1_tarski(X6,k2_xboole_0(X8,X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_20,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( v5_relat_1(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_15])).

cnf(c_0_23,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v4_relat_1(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_15])).

fof(c_0_25,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | ~ r1_tarski(X11,X10)
      | r1_tarski(k2_xboole_0(X9,X11),X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_22])])).

fof(c_0_29,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_30,plain,(
    ! [X16] :
      ( ~ v1_relat_1(X16)
      | k3_relat_1(X16) = k2_xboole_0(k1_relat_1(X16),k2_relat_1(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

cnf(c_0_31,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk3_0),k2_xboole_0(X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),k2_xboole_0(X1,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_28])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk3_0),k2_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,k2_relat_1(esk3_0)),k2_xboole_0(X2,esk2_0))
    | ~ r1_tarski(X1,k2_xboole_0(X2,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),k2_xboole_0(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k1_relat_1(esk3_0),k2_relat_1(esk3_0)),k2_xboole_0(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_22])])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 21:04:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  # Version: 2.5pre002
% 0.15/0.36  # No SInE strategy applied
% 0.15/0.36  # Trying AutoSched0 for 299 seconds
% 0.15/0.39  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.15/0.39  # and selection function SelectCQIPrecWNTNp.
% 0.15/0.39  #
% 0.15/0.39  # Preprocessing time       : 0.027 s
% 0.15/0.39  # Presaturation interreduction done
% 0.15/0.39  
% 0.15/0.39  # Proof found!
% 0.15/0.39  # SZS status Theorem
% 0.15/0.39  # SZS output start CNFRefutation
% 0.15/0.39  fof(t19_relset_1, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>r1_tarski(k3_relat_1(X3),k2_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relset_1)).
% 0.15/0.39  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.15/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.15/0.39  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.15/0.39  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.15/0.39  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.15/0.39  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.15/0.39  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.15/0.39  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 0.15/0.39  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>r1_tarski(k3_relat_1(X3),k2_xboole_0(X1,X2)))), inference(assume_negation,[status(cth)],[t19_relset_1])).
% 0.15/0.39  fof(c_0_10, plain, ![X20, X21, X22]:((v4_relat_1(X22,X20)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))&(v5_relat_1(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.15/0.39  fof(c_0_11, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))&~r1_tarski(k3_relat_1(esk3_0),k2_xboole_0(esk1_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.15/0.39  fof(c_0_12, plain, ![X17, X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))|v1_relat_1(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.15/0.39  fof(c_0_13, plain, ![X14, X15]:((~v5_relat_1(X15,X14)|r1_tarski(k2_relat_1(X15),X14)|~v1_relat_1(X15))&(~r1_tarski(k2_relat_1(X15),X14)|v5_relat_1(X15,X14)|~v1_relat_1(X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.15/0.39  cnf(c_0_14, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.15/0.39  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.39  cnf(c_0_16, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.15/0.39  fof(c_0_17, plain, ![X12, X13]:((~v4_relat_1(X13,X12)|r1_tarski(k1_relat_1(X13),X12)|~v1_relat_1(X13))&(~r1_tarski(k1_relat_1(X13),X12)|v4_relat_1(X13,X12)|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.15/0.39  cnf(c_0_18, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.15/0.39  fof(c_0_19, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|r1_tarski(X6,k2_xboole_0(X8,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.15/0.39  cnf(c_0_20, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.39  cnf(c_0_21, negated_conjecture, (v5_relat_1(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.15/0.39  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_16, c_0_15])).
% 0.15/0.39  cnf(c_0_23, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.15/0.39  cnf(c_0_24, negated_conjecture, (v4_relat_1(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_18, c_0_15])).
% 0.15/0.39  fof(c_0_25, plain, ![X9, X10, X11]:(~r1_tarski(X9,X10)|~r1_tarski(X11,X10)|r1_tarski(k2_xboole_0(X9,X11),X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.15/0.39  cnf(c_0_26, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.15/0.39  cnf(c_0_27, negated_conjecture, (r1_tarski(k2_relat_1(esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.15/0.39  cnf(c_0_28, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_22])])).
% 0.15/0.39  fof(c_0_29, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.15/0.39  fof(c_0_30, plain, ![X16]:(~v1_relat_1(X16)|k3_relat_1(X16)=k2_xboole_0(k1_relat_1(X16),k2_relat_1(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 0.15/0.39  cnf(c_0_31, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.15/0.39  cnf(c_0_32, negated_conjecture, (r1_tarski(k2_relat_1(esk3_0),k2_xboole_0(X1,esk2_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.15/0.39  cnf(c_0_33, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),k2_xboole_0(X1,esk1_0))), inference(spm,[status(thm)],[c_0_26, c_0_28])).
% 0.15/0.39  cnf(c_0_34, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.15/0.39  cnf(c_0_35, negated_conjecture, (~r1_tarski(k3_relat_1(esk3_0),k2_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.39  cnf(c_0_36, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.15/0.39  cnf(c_0_37, negated_conjecture, (r1_tarski(k2_xboole_0(X1,k2_relat_1(esk3_0)),k2_xboole_0(X2,esk2_0))|~r1_tarski(X1,k2_xboole_0(X2,esk2_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.15/0.39  cnf(c_0_38, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),k2_xboole_0(esk1_0,X1))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.15/0.39  cnf(c_0_39, negated_conjecture, (~r1_tarski(k2_xboole_0(k1_relat_1(esk3_0),k2_relat_1(esk3_0)),k2_xboole_0(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_22])])).
% 0.15/0.39  cnf(c_0_40, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), ['proof']).
% 0.15/0.39  # SZS output end CNFRefutation
% 0.15/0.39  # Proof object total steps             : 41
% 0.15/0.39  # Proof object clause steps            : 22
% 0.15/0.39  # Proof object formula steps           : 19
% 0.15/0.39  # Proof object conjectures             : 16
% 0.15/0.39  # Proof object clause conjectures      : 13
% 0.15/0.39  # Proof object formula conjectures     : 3
% 0.15/0.39  # Proof object initial clauses used    : 11
% 0.15/0.39  # Proof object initial formulas used   : 9
% 0.15/0.39  # Proof object generating inferences   : 11
% 0.15/0.39  # Proof object simplifying inferences  : 7
% 0.15/0.39  # Training examples: 0 positive, 0 negative
% 0.15/0.39  # Parsed axioms                        : 9
% 0.15/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.39  # Initial clauses                      : 13
% 0.15/0.39  # Removed in clause preprocessing      : 0
% 0.15/0.39  # Initial clauses in saturation        : 13
% 0.15/0.39  # Processed clauses                    : 64
% 0.15/0.39  # ...of these trivial                  : 11
% 0.15/0.39  # ...subsumed                          : 0
% 0.15/0.39  # ...remaining for further processing  : 53
% 0.15/0.39  # Other redundant clauses eliminated   : 0
% 0.15/0.39  # Clauses deleted for lack of memory   : 0
% 0.15/0.39  # Backward-subsumed                    : 0
% 0.15/0.39  # Backward-rewritten                   : 0
% 0.15/0.39  # Generated clauses                    : 97
% 0.15/0.39  # ...of the previous two non-trivial   : 69
% 0.15/0.39  # Contextual simplify-reflections      : 0
% 0.15/0.39  # Paramodulations                      : 97
% 0.15/0.39  # Factorizations                       : 0
% 0.15/0.39  # Equation resolutions                 : 0
% 0.15/0.39  # Propositional unsat checks           : 0
% 0.15/0.39  #    Propositional check models        : 0
% 0.15/0.39  #    Propositional check unsatisfiable : 0
% 0.15/0.39  #    Propositional clauses             : 0
% 0.15/0.39  #    Propositional clauses after purity: 0
% 0.15/0.39  #    Propositional unsat core size     : 0
% 0.15/0.39  #    Propositional preprocessing time  : 0.000
% 0.15/0.39  #    Propositional encoding time       : 0.000
% 0.15/0.39  #    Propositional solver time         : 0.000
% 0.15/0.39  #    Success case prop preproc time    : 0.000
% 0.15/0.39  #    Success case prop encoding time   : 0.000
% 0.15/0.39  #    Success case prop solver time     : 0.000
% 0.15/0.39  # Current number of processed clauses  : 40
% 0.15/0.39  #    Positive orientable unit clauses  : 21
% 0.15/0.39  #    Positive unorientable unit clauses: 1
% 0.15/0.39  #    Negative unit clauses             : 2
% 0.15/0.39  #    Non-unit-clauses                  : 16
% 0.15/0.39  # Current number of unprocessed clauses: 27
% 0.15/0.39  # ...number of literals in the above   : 32
% 0.15/0.39  # Current number of archived formulas  : 0
% 0.15/0.39  # Current number of archived clauses   : 13
% 0.15/0.39  # Clause-clause subsumption calls (NU) : 18
% 0.15/0.39  # Rec. Clause-clause subsumption calls : 18
% 0.15/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.15/0.39  # Unit Clause-clause subsumption calls : 15
% 0.15/0.39  # Rewrite failures with RHS unbound    : 0
% 0.15/0.39  # BW rewrite match attempts            : 6
% 0.15/0.39  # BW rewrite match successes           : 4
% 0.15/0.39  # Condensation attempts                : 0
% 0.15/0.39  # Condensation successes               : 0
% 0.15/0.39  # Termbank termtop insertions          : 2068
% 0.15/0.39  
% 0.15/0.39  # -------------------------------------------------
% 0.15/0.39  # User time                : 0.030 s
% 0.15/0.39  # System time              : 0.002 s
% 0.15/0.39  # Total time               : 0.032 s
% 0.15/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
