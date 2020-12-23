%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:57:43 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   40 (  91 expanded)
%              Number of clauses        :   23 (  37 expanded)
%              Number of leaves         :    8 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :   91 ( 221 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_relset_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
     => ( r1_tarski(X2,X3)
       => r2_relset_1(X2,X1,k5_relset_1(X2,X1,X4,X3),X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

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

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(reflexivity_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => r2_relset_1(X1,X2,X3,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(redefinition_k5_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k5_relset_1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
       => ( r1_tarski(X2,X3)
         => r2_relset_1(X2,X1,k5_relset_1(X2,X1,X4,X3),X4) ) ) ),
    inference(assume_negation,[status(cth)],[t34_relset_1])).

fof(c_0_9,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(X5,X6)
      | ~ r1_tarski(X6,X7)
      | r1_tarski(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_10,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))
    & r1_tarski(esk2_0,esk3_0)
    & ~ r2_relset_1(esk2_0,esk1_0,k5_relset_1(esk2_0,esk1_0,esk4_0,esk3_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X15,X16,X17] :
      ( ( v4_relat_1(X17,X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( v5_relat_1(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_12,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | v1_relat_1(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_13,plain,(
    ! [X8,X9] :
      ( ( ~ v4_relat_1(X9,X8)
        | r1_tarski(k1_relat_1(X9),X8)
        | ~ v1_relat_1(X9) )
      & ( ~ r1_tarski(k1_relat_1(X9),X8)
        | v4_relat_1(X9,X8)
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( v4_relat_1(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( v4_relat_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v4_relat_1(X1,esk3_0)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

fof(c_0_26,plain,(
    ! [X22,X23,X24,X25] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | r2_relset_1(X22,X23,X24,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_relset_1])])).

fof(c_0_27,plain,(
    ! [X18,X19,X20,X21] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | k5_relset_1(X18,X19,X20,X21) = k7_relat_1(X20,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_relset_1])])).

fof(c_0_28,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X11)
      | ~ r1_tarski(k1_relat_1(X11),X10)
      | k7_relat_1(X11,X10) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_29,negated_conjecture,
    ( v4_relat_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_23])])).

cnf(c_0_30,plain,
    ( r2_relset_1(X2,X3,X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( k5_relset_1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_29]),c_0_23])])).

cnf(c_0_34,negated_conjecture,
    ( r2_relset_1(esk2_0,esk1_0,X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_17])).

cnf(c_0_35,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk1_0,k5_relset_1(esk2_0,esk1_0,esk4_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_36,negated_conjecture,
    ( k5_relset_1(esk2_0,esk1_0,esk4_0,X1) = k7_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_17])).

cnf(c_0_37,negated_conjecture,
    ( k7_relat_1(esk4_0,esk3_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_23])])).

cnf(c_0_38,negated_conjecture,
    ( r2_relset_1(esk2_0,esk1_0,esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_17])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.07/0.26  % Computer   : n016.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % WCLimit    : 600
% 0.07/0.26  % DateTime   : Tue Dec  1 19:06:49 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.07/0.26  # Version: 2.5pre002
% 0.07/0.26  # No SInE strategy applied
% 0.07/0.26  # Trying AutoSched0 for 299 seconds
% 0.11/0.29  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S087N
% 0.11/0.29  # and selection function SelectCQArNpEqFirstUnlessPDom.
% 0.11/0.29  #
% 0.11/0.29  # Preprocessing time       : 0.027 s
% 0.11/0.29  # Presaturation interreduction done
% 0.11/0.29  
% 0.11/0.29  # Proof found!
% 0.11/0.29  # SZS status Theorem
% 0.11/0.29  # SZS output start CNFRefutation
% 0.11/0.29  fof(t34_relset_1, conjecture, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>(r1_tarski(X2,X3)=>r2_relset_1(X2,X1,k5_relset_1(X2,X1,X4,X3),X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relset_1)).
% 0.11/0.29  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.11/0.29  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.11/0.29  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.11/0.29  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.11/0.29  fof(reflexivity_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r2_relset_1(X1,X2,X3,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 0.11/0.29  fof(redefinition_k5_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k5_relset_1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 0.11/0.29  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 0.11/0.29  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>(r1_tarski(X2,X3)=>r2_relset_1(X2,X1,k5_relset_1(X2,X1,X4,X3),X4)))), inference(assume_negation,[status(cth)],[t34_relset_1])).
% 0.11/0.29  fof(c_0_9, plain, ![X5, X6, X7]:(~r1_tarski(X5,X6)|~r1_tarski(X6,X7)|r1_tarski(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.11/0.29  fof(c_0_10, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))&(r1_tarski(esk2_0,esk3_0)&~r2_relset_1(esk2_0,esk1_0,k5_relset_1(esk2_0,esk1_0,esk4_0,esk3_0),esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.11/0.29  fof(c_0_11, plain, ![X15, X16, X17]:((v4_relat_1(X17,X15)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))))&(v5_relat_1(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.11/0.29  fof(c_0_12, plain, ![X12, X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))|v1_relat_1(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.11/0.29  fof(c_0_13, plain, ![X8, X9]:((~v4_relat_1(X9,X8)|r1_tarski(k1_relat_1(X9),X8)|~v1_relat_1(X9))&(~r1_tarski(k1_relat_1(X9),X8)|v4_relat_1(X9,X8)|~v1_relat_1(X9))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.11/0.29  cnf(c_0_14, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.11/0.29  cnf(c_0_15, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.11/0.29  cnf(c_0_16, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.11/0.29  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.11/0.29  cnf(c_0_18, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.29  cnf(c_0_19, plain, (v4_relat_1(X1,X2)|~r1_tarski(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.11/0.29  cnf(c_0_20, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.11/0.29  cnf(c_0_21, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.11/0.29  cnf(c_0_22, negated_conjecture, (v4_relat_1(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.11/0.29  cnf(c_0_23, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_18, c_0_17])).
% 0.11/0.29  cnf(c_0_24, negated_conjecture, (v4_relat_1(X1,esk3_0)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),esk2_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.11/0.29  cnf(c_0_25, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.11/0.29  fof(c_0_26, plain, ![X22, X23, X24, X25]:(~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|r2_relset_1(X22,X23,X24,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_relset_1])])).
% 0.11/0.29  fof(c_0_27, plain, ![X18, X19, X20, X21]:(~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))|k5_relset_1(X18,X19,X20,X21)=k7_relat_1(X20,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_relset_1])])).
% 0.11/0.29  fof(c_0_28, plain, ![X10, X11]:(~v1_relat_1(X11)|(~r1_tarski(k1_relat_1(X11),X10)|k7_relat_1(X11,X10)=X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.11/0.29  cnf(c_0_29, negated_conjecture, (v4_relat_1(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_23])])).
% 0.11/0.29  cnf(c_0_30, plain, (r2_relset_1(X2,X3,X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.11/0.29  cnf(c_0_31, plain, (k5_relset_1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.11/0.29  cnf(c_0_32, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.11/0.29  cnf(c_0_33, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_29]), c_0_23])])).
% 0.11/0.29  cnf(c_0_34, negated_conjecture, (r2_relset_1(esk2_0,esk1_0,X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(spm,[status(thm)],[c_0_30, c_0_17])).
% 0.11/0.29  cnf(c_0_35, negated_conjecture, (~r2_relset_1(esk2_0,esk1_0,k5_relset_1(esk2_0,esk1_0,esk4_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.11/0.29  cnf(c_0_36, negated_conjecture, (k5_relset_1(esk2_0,esk1_0,esk4_0,X1)=k7_relat_1(esk4_0,X1)), inference(spm,[status(thm)],[c_0_31, c_0_17])).
% 0.11/0.29  cnf(c_0_37, negated_conjecture, (k7_relat_1(esk4_0,esk3_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_23])])).
% 0.11/0.29  cnf(c_0_38, negated_conjecture, (r2_relset_1(esk2_0,esk1_0,esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_34, c_0_17])).
% 0.11/0.29  cnf(c_0_39, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38])]), ['proof']).
% 0.11/0.29  # SZS output end CNFRefutation
% 0.11/0.29  # Proof object total steps             : 40
% 0.11/0.29  # Proof object clause steps            : 23
% 0.11/0.29  # Proof object formula steps           : 17
% 0.11/0.29  # Proof object conjectures             : 18
% 0.11/0.29  # Proof object clause conjectures      : 15
% 0.11/0.29  # Proof object formula conjectures     : 3
% 0.11/0.29  # Proof object initial clauses used    : 11
% 0.11/0.29  # Proof object initial formulas used   : 8
% 0.11/0.29  # Proof object generating inferences   : 11
% 0.11/0.29  # Proof object simplifying inferences  : 12
% 0.11/0.29  # Training examples: 0 positive, 0 negative
% 0.11/0.29  # Parsed axioms                        : 8
% 0.11/0.29  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.29  # Initial clauses                      : 12
% 0.11/0.29  # Removed in clause preprocessing      : 0
% 0.11/0.29  # Initial clauses in saturation        : 12
% 0.11/0.29  # Processed clauses                    : 40
% 0.11/0.29  # ...of these trivial                  : 0
% 0.11/0.29  # ...subsumed                          : 0
% 0.11/0.29  # ...remaining for further processing  : 40
% 0.11/0.29  # Other redundant clauses eliminated   : 0
% 0.11/0.29  # Clauses deleted for lack of memory   : 0
% 0.11/0.29  # Backward-subsumed                    : 0
% 0.11/0.29  # Backward-rewritten                   : 1
% 0.11/0.29  # Generated clauses                    : 34
% 0.11/0.29  # ...of the previous two non-trivial   : 32
% 0.11/0.29  # Contextual simplify-reflections      : 0
% 0.11/0.29  # Paramodulations                      : 34
% 0.11/0.29  # Factorizations                       : 0
% 0.11/0.29  # Equation resolutions                 : 0
% 0.11/0.29  # Propositional unsat checks           : 0
% 0.11/0.29  #    Propositional check models        : 0
% 0.11/0.29  #    Propositional check unsatisfiable : 0
% 0.11/0.29  #    Propositional clauses             : 0
% 0.11/0.29  #    Propositional clauses after purity: 0
% 0.11/0.29  #    Propositional unsat core size     : 0
% 0.11/0.29  #    Propositional preprocessing time  : 0.000
% 0.11/0.29  #    Propositional encoding time       : 0.000
% 0.11/0.29  #    Propositional solver time         : 0.000
% 0.11/0.29  #    Success case prop preproc time    : 0.000
% 0.11/0.29  #    Success case prop encoding time   : 0.000
% 0.11/0.29  #    Success case prop solver time     : 0.000
% 0.11/0.29  # Current number of processed clauses  : 27
% 0.11/0.29  #    Positive orientable unit clauses  : 12
% 0.11/0.29  #    Positive unorientable unit clauses: 0
% 0.11/0.29  #    Negative unit clauses             : 0
% 0.11/0.29  #    Non-unit-clauses                  : 15
% 0.11/0.29  # Current number of unprocessed clauses: 16
% 0.11/0.29  # ...number of literals in the above   : 53
% 0.11/0.29  # Current number of archived formulas  : 0
% 0.11/0.29  # Current number of archived clauses   : 13
% 0.11/0.29  # Clause-clause subsumption calls (NU) : 20
% 0.11/0.29  # Rec. Clause-clause subsumption calls : 18
% 0.11/0.29  # Non-unit clause-clause subsumptions  : 0
% 0.11/0.29  # Unit Clause-clause subsumption calls : 15
% 0.11/0.29  # Rewrite failures with RHS unbound    : 0
% 0.11/0.29  # BW rewrite match attempts            : 3
% 0.11/0.29  # BW rewrite match successes           : 1
% 0.11/0.29  # Condensation attempts                : 0
% 0.11/0.29  # Condensation successes               : 0
% 0.11/0.29  # Termbank termtop insertions          : 1399
% 0.11/0.29  
% 0.11/0.29  # -------------------------------------------------
% 0.11/0.29  # User time                : 0.029 s
% 0.11/0.29  # System time              : 0.002 s
% 0.11/0.29  # Total time               : 0.032 s
% 0.11/0.29  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
