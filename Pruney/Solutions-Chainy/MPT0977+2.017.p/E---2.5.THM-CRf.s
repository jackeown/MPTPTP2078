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
% DateTime   : Thu Dec  3 11:01:55 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 103 expanded)
%              Number of clauses        :   26 (  41 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  110 ( 235 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)
        & r2_relset_1(X1,X2,k4_relset_1(X1,X2,X2,X2,X3,k6_partfun1(X2)),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(redefinition_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k4_relset_1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(t29_relset_1,axiom,(
    ! [X1] : m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(t79_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k5_relat_1(X2,k6_relat_1(X1)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(reflexivity_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => r2_relset_1(X1,X2,X3,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => ( r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)
          & r2_relset_1(X1,X2,k4_relset_1(X1,X2,X2,X2,X3,k6_partfun1(X2)),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t23_funct_2])).

fof(c_0_12,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & ( ~ r2_relset_1(esk1_0,esk2_0,k4_relset_1(esk1_0,esk1_0,esk1_0,esk2_0,k6_partfun1(esk1_0),esk3_0),esk3_0)
      | ~ r2_relset_1(esk1_0,esk2_0,k4_relset_1(esk1_0,esk2_0,esk2_0,esk2_0,esk3_0,k6_partfun1(esk2_0)),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_13,plain,(
    ! [X32] : k6_partfun1(X32) = k6_relat_1(X32) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_14,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk2_0,k4_relset_1(esk1_0,esk1_0,esk1_0,esk2_0,k6_partfun1(esk1_0),esk3_0),esk3_0)
    | ~ r2_relset_1(esk1_0,esk2_0,k4_relset_1(esk1_0,esk2_0,esk2_0,esk2_0,esk3_0,k6_partfun1(esk2_0)),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,plain,(
    ! [X21,X22,X23,X24,X25,X26] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | k4_relset_1(X21,X22,X23,X24,X25,X26) = k5_relat_1(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).

fof(c_0_17,plain,(
    ! [X31] : m1_subset_1(k6_relat_1(X31),k1_zfmisc_1(k2_zfmisc_1(X31,X31))) ),
    inference(variable_rename,[status(thm)],[t29_relset_1])).

cnf(c_0_18,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk2_0,k4_relset_1(esk1_0,esk2_0,esk2_0,esk2_0,esk3_0,k6_relat_1(esk2_0)),esk3_0)
    | ~ r2_relset_1(esk1_0,esk2_0,k4_relset_1(esk1_0,esk1_0,esk1_0,esk2_0,k6_relat_1(esk1_0),esk3_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_15])).

cnf(c_0_19,plain,
    ( k4_relset_1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_22,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | v1_relat_1(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_23,plain,(
    ! [X18,X19,X20] :
      ( ( v4_relat_1(X20,X18)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( v5_relat_1(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk2_0,k4_relset_1(esk1_0,esk1_0,esk1_0,esk2_0,k6_relat_1(esk1_0),esk3_0),esk3_0)
    | ~ r2_relset_1(esk1_0,esk2_0,k5_relat_1(esk3_0,k6_relat_1(esk2_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])])).

fof(c_0_25,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X14)
      | k7_relat_1(X14,X13) = k5_relat_1(k6_relat_1(X13),X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_26,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_27,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X10)
      | ~ v4_relat_1(X10,X9)
      | X10 = k7_relat_1(X10,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_28,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk2_0,k5_relat_1(k6_relat_1(esk1_0),esk3_0),esk3_0)
    | ~ r2_relset_1(esk1_0,esk2_0,k5_relat_1(esk3_0,k6_relat_1(esk2_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_19]),c_0_21]),c_0_20])])).

cnf(c_0_30,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_21])).

cnf(c_0_32,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( v4_relat_1(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_21])).

fof(c_0_34,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X12)
      | ~ r1_tarski(k2_relat_1(X12),X11)
      | k5_relat_1(X12,k6_relat_1(X11)) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).

fof(c_0_35,plain,(
    ! [X7,X8] :
      ( ( ~ v5_relat_1(X8,X7)
        | r1_tarski(k2_relat_1(X8),X7)
        | ~ v1_relat_1(X8) )
      & ( ~ r1_tarski(k2_relat_1(X8),X7)
        | v5_relat_1(X8,X7)
        | ~ v1_relat_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_36,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk2_0,k5_relat_1(esk3_0,k6_relat_1(esk2_0)),esk3_0)
    | ~ r2_relset_1(esk1_0,esk2_0,k7_relat_1(esk3_0,esk1_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

cnf(c_0_37,negated_conjecture,
    ( k7_relat_1(esk3_0,esk1_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_31])])).

cnf(c_0_38,plain,
    ( k5_relat_1(X1,k6_relat_1(X2)) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_41,plain,(
    ! [X27,X28,X29,X30] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | r2_relset_1(X27,X28,X29,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_relset_1])])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk2_0,k5_relat_1(esk3_0,k6_relat_1(esk2_0)),esk3_0)
    | ~ r2_relset_1(esk1_0,esk2_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( k5_relat_1(X1,k6_relat_1(X2)) = X1
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( v5_relat_1(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_21])).

cnf(c_0_45,plain,
    ( r2_relset_1(X2,X3,X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk2_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_31])])).

cnf(c_0_47,negated_conjecture,
    ( r2_relset_1(esk1_0,esk2_0,X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_21])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:04:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t23_funct_2, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)&r2_relset_1(X1,X2,k4_relset_1(X1,X2,X2,X2,X3,k6_partfun1(X2)),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_2)).
% 0.13/0.37  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.13/0.37  fof(redefinition_k4_relset_1, axiom, ![X1, X2, X3, X4, X5, X6]:((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k4_relset_1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 0.13/0.37  fof(t29_relset_1, axiom, ![X1]:m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 0.13/0.37  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.13/0.37  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.13/0.37  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 0.13/0.37  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 0.13/0.37  fof(t79_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k5_relat_1(X2,k6_relat_1(X1))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 0.13/0.37  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.13/0.37  fof(reflexivity_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r2_relset_1(X1,X2,X3,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 0.13/0.37  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)&r2_relset_1(X1,X2,k4_relset_1(X1,X2,X2,X2,X3,k6_partfun1(X2)),X3)))), inference(assume_negation,[status(cth)],[t23_funct_2])).
% 0.13/0.37  fof(c_0_12, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))&(~r2_relset_1(esk1_0,esk2_0,k4_relset_1(esk1_0,esk1_0,esk1_0,esk2_0,k6_partfun1(esk1_0),esk3_0),esk3_0)|~r2_relset_1(esk1_0,esk2_0,k4_relset_1(esk1_0,esk2_0,esk2_0,esk2_0,esk3_0,k6_partfun1(esk2_0)),esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.13/0.37  fof(c_0_13, plain, ![X32]:k6_partfun1(X32)=k6_relat_1(X32), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.13/0.37  cnf(c_0_14, negated_conjecture, (~r2_relset_1(esk1_0,esk2_0,k4_relset_1(esk1_0,esk1_0,esk1_0,esk2_0,k6_partfun1(esk1_0),esk3_0),esk3_0)|~r2_relset_1(esk1_0,esk2_0,k4_relset_1(esk1_0,esk2_0,esk2_0,esk2_0,esk3_0,k6_partfun1(esk2_0)),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_15, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  fof(c_0_16, plain, ![X21, X22, X23, X24, X25, X26]:(~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|k4_relset_1(X21,X22,X23,X24,X25,X26)=k5_relat_1(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).
% 0.13/0.37  fof(c_0_17, plain, ![X31]:m1_subset_1(k6_relat_1(X31),k1_zfmisc_1(k2_zfmisc_1(X31,X31))), inference(variable_rename,[status(thm)],[t29_relset_1])).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (~r2_relset_1(esk1_0,esk2_0,k4_relset_1(esk1_0,esk2_0,esk2_0,esk2_0,esk3_0,k6_relat_1(esk2_0)),esk3_0)|~r2_relset_1(esk1_0,esk2_0,k4_relset_1(esk1_0,esk1_0,esk1_0,esk2_0,k6_relat_1(esk1_0),esk3_0),esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_15]), c_0_15])).
% 0.13/0.37  cnf(c_0_19, plain, (k4_relset_1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_20, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  fof(c_0_22, plain, ![X15, X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))|v1_relat_1(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.13/0.37  fof(c_0_23, plain, ![X18, X19, X20]:((v4_relat_1(X20,X18)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))&(v5_relat_1(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (~r2_relset_1(esk1_0,esk2_0,k4_relset_1(esk1_0,esk1_0,esk1_0,esk2_0,k6_relat_1(esk1_0),esk3_0),esk3_0)|~r2_relset_1(esk1_0,esk2_0,k5_relat_1(esk3_0,k6_relat_1(esk2_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21])])).
% 0.13/0.37  fof(c_0_25, plain, ![X13, X14]:(~v1_relat_1(X14)|k7_relat_1(X14,X13)=k5_relat_1(k6_relat_1(X13),X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.13/0.37  cnf(c_0_26, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.37  fof(c_0_27, plain, ![X9, X10]:(~v1_relat_1(X10)|~v4_relat_1(X10,X9)|X10=k7_relat_1(X10,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.13/0.37  cnf(c_0_28, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.37  cnf(c_0_29, negated_conjecture, (~r2_relset_1(esk1_0,esk2_0,k5_relat_1(k6_relat_1(esk1_0),esk3_0),esk3_0)|~r2_relset_1(esk1_0,esk2_0,k5_relat_1(esk3_0,k6_relat_1(esk2_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_19]), c_0_21]), c_0_20])])).
% 0.13/0.37  cnf(c_0_30, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.37  cnf(c_0_31, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_21])).
% 0.13/0.37  cnf(c_0_32, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.37  cnf(c_0_33, negated_conjecture, (v4_relat_1(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_28, c_0_21])).
% 0.13/0.37  fof(c_0_34, plain, ![X11, X12]:(~v1_relat_1(X12)|(~r1_tarski(k2_relat_1(X12),X11)|k5_relat_1(X12,k6_relat_1(X11))=X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).
% 0.13/0.37  fof(c_0_35, plain, ![X7, X8]:((~v5_relat_1(X8,X7)|r1_tarski(k2_relat_1(X8),X7)|~v1_relat_1(X8))&(~r1_tarski(k2_relat_1(X8),X7)|v5_relat_1(X8,X7)|~v1_relat_1(X8))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.13/0.37  cnf(c_0_36, negated_conjecture, (~r2_relset_1(esk1_0,esk2_0,k5_relat_1(esk3_0,k6_relat_1(esk2_0)),esk3_0)|~r2_relset_1(esk1_0,esk2_0,k7_relat_1(esk3_0,esk1_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 0.13/0.37  cnf(c_0_37, negated_conjecture, (k7_relat_1(esk3_0,esk1_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_31])])).
% 0.13/0.37  cnf(c_0_38, plain, (k5_relat_1(X1,k6_relat_1(X2))=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.37  cnf(c_0_39, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.37  cnf(c_0_40, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.37  fof(c_0_41, plain, ![X27, X28, X29, X30]:(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|r2_relset_1(X27,X28,X29,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_relset_1])])).
% 0.13/0.37  cnf(c_0_42, negated_conjecture, (~r2_relset_1(esk1_0,esk2_0,k5_relat_1(esk3_0,k6_relat_1(esk2_0)),esk3_0)|~r2_relset_1(esk1_0,esk2_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.37  cnf(c_0_43, plain, (k5_relat_1(X1,k6_relat_1(X2))=X1|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.37  cnf(c_0_44, negated_conjecture, (v5_relat_1(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_40, c_0_21])).
% 0.13/0.37  cnf(c_0_45, plain, (r2_relset_1(X2,X3,X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.37  cnf(c_0_46, negated_conjecture, (~r2_relset_1(esk1_0,esk2_0,esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_31])])).
% 0.13/0.37  cnf(c_0_47, negated_conjecture, (r2_relset_1(esk1_0,esk2_0,X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_45, c_0_21])).
% 0.13/0.37  cnf(c_0_48, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_21])]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 49
% 0.13/0.37  # Proof object clause steps            : 26
% 0.13/0.37  # Proof object formula steps           : 23
% 0.13/0.37  # Proof object conjectures             : 17
% 0.13/0.37  # Proof object clause conjectures      : 14
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 13
% 0.13/0.37  # Proof object initial formulas used   : 11
% 0.13/0.37  # Proof object generating inferences   : 11
% 0.13/0.37  # Proof object simplifying inferences  : 18
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 11
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 14
% 0.13/0.37  # Removed in clause preprocessing      : 1
% 0.13/0.37  # Initial clauses in saturation        : 13
% 0.13/0.37  # Processed clauses                    : 41
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 41
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 1
% 0.13/0.37  # Generated clauses                    : 18
% 0.13/0.37  # ...of the previous two non-trivial   : 17
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 18
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 27
% 0.13/0.37  #    Positive orientable unit clauses  : 10
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 1
% 0.13/0.37  #    Non-unit-clauses                  : 16
% 0.13/0.37  # Current number of unprocessed clauses: 2
% 0.13/0.37  # ...number of literals in the above   : 4
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 15
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 44
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 41
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 14
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 1
% 0.13/0.37  # BW rewrite match successes           : 1
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1516
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.025 s
% 0.13/0.37  # System time              : 0.007 s
% 0.13/0.37  # Total time               : 0.033 s
% 0.13/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
