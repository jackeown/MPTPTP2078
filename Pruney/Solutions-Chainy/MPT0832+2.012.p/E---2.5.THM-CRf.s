%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:57:52 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 110 expanded)
%              Number of clauses        :   25 (  49 expanded)
%              Number of leaves         :   10 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :   89 ( 209 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t35_relset_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
     => m1_subset_1(k6_relset_1(X3,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t4_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
     => ( r1_tarski(X1,X4)
       => m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).

fof(t117_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k8_relat_1(X1,X2),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t116_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(redefinition_k6_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k6_relset_1(X1,X2,X3,X4) = k8_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
       => m1_subset_1(k6_relset_1(X3,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ),
    inference(assume_negation,[status(cth)],[t35_relset_1])).

fof(c_0_11,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | v1_relat_1(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_12,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0)))
    & ~ m1_subset_1(k6_relset_1(esk3_0,esk1_0,esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_13,plain,(
    ! [X29,X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | ~ r1_tarski(X29,X32)
      | m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_relset_1])])).

fof(c_0_14,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X12)
      | r1_tarski(k8_relat_1(X11,X12),X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_relat_1])])).

cnf(c_0_15,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r1_tarski(k8_relat_1(X2,X1),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_20,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | k1_relset_1(X19,X20,X21) = k1_relat_1(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(k8_relat_1(X1,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_23,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X10)
      | r1_tarski(k2_relat_1(k8_relat_1(X9,X10)),X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t116_relat_1])])).

fof(c_0_24,plain,(
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | m1_subset_1(k1_relset_1(X16,X17,X18),k1_zfmisc_1(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

cnf(c_0_25,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(k8_relat_1(X1,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_27,plain,(
    ! [X22,X23,X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | k6_relset_1(X22,X23,X24,X25) = k8_relat_1(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_relset_1])])).

fof(c_0_28,plain,(
    ! [X26,X27,X28] :
      ( ~ v1_relat_1(X28)
      | ~ r1_tarski(k1_relat_1(X28),X26)
      | ~ r1_tarski(k2_relat_1(X28),X27)
      | m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_29,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X2,X1)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X7,X8] :
      ( ( ~ m1_subset_1(X7,k1_zfmisc_1(X8))
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | m1_subset_1(X7,k1_zfmisc_1(X8)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_31,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( k1_relset_1(esk3_0,esk1_0,k8_relat_1(X1,esk4_0)) = k1_relat_1(k8_relat_1(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( k6_relset_1(X2,X3,X4,X1) = k8_relat_1(X4,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k2_relat_1(k8_relat_1(X1,esk4_0)),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_19])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(k8_relat_1(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_26])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(k1_relat_1(k8_relat_1(X1,esk4_0)),k1_zfmisc_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_26])])).

cnf(c_0_39,negated_conjecture,
    ( ~ m1_subset_1(k6_relset_1(esk3_0,esk1_0,esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_40,negated_conjecture,
    ( k6_relset_1(esk3_0,esk1_0,X1,esk4_0) = k8_relat_1(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_16])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(k8_relat_1(X1,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ r1_tarski(k1_relat_1(k8_relat_1(X1,esk4_0)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k1_relat_1(k8_relat_1(X1,esk4_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( ~ m1_subset_1(k8_relat_1(esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(k8_relat_1(X1,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n010.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 12:31:29 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.17/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S087N
% 0.17/0.42  # and selection function SelectCQArNpEqFirstUnlessPDom.
% 0.17/0.42  #
% 0.17/0.42  # Preprocessing time       : 0.045 s
% 0.17/0.42  # Presaturation interreduction done
% 0.17/0.42  
% 0.17/0.42  # Proof found!
% 0.17/0.42  # SZS status Theorem
% 0.17/0.42  # SZS output start CNFRefutation
% 0.17/0.42  fof(t35_relset_1, conjecture, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>m1_subset_1(k6_relset_1(X3,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_relset_1)).
% 0.17/0.42  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.17/0.42  fof(t4_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))=>(r1_tarski(X1,X4)=>m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_relset_1)).
% 0.17/0.42  fof(t117_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k8_relat_1(X1,X2),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 0.17/0.42  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.17/0.42  fof(t116_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 0.17/0.42  fof(dt_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 0.17/0.42  fof(redefinition_k6_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k6_relset_1(X1,X2,X3,X4)=k8_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 0.17/0.42  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 0.17/0.42  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.17/0.42  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>m1_subset_1(k6_relset_1(X3,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X3,X2))))), inference(assume_negation,[status(cth)],[t35_relset_1])).
% 0.17/0.42  fof(c_0_11, plain, ![X13, X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|v1_relat_1(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.17/0.42  fof(c_0_12, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0)))&~m1_subset_1(k6_relset_1(esk3_0,esk1_0,esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.17/0.42  fof(c_0_13, plain, ![X29, X30, X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|(~r1_tarski(X29,X32)|m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_relset_1])])).
% 0.17/0.42  fof(c_0_14, plain, ![X11, X12]:(~v1_relat_1(X12)|r1_tarski(k8_relat_1(X11,X12),X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_relat_1])])).
% 0.17/0.42  cnf(c_0_15, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.42  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.17/0.42  cnf(c_0_17, plain, (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.42  cnf(c_0_18, plain, (r1_tarski(k8_relat_1(X2,X1),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.17/0.42  cnf(c_0_19, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.17/0.42  fof(c_0_20, plain, ![X19, X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|k1_relset_1(X19,X20,X21)=k1_relat_1(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.17/0.42  cnf(c_0_21, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0)))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_17, c_0_16])).
% 0.17/0.42  cnf(c_0_22, negated_conjecture, (r1_tarski(k8_relat_1(X1,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.17/0.42  fof(c_0_23, plain, ![X9, X10]:(~v1_relat_1(X10)|r1_tarski(k2_relat_1(k8_relat_1(X9,X10)),X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t116_relat_1])])).
% 0.17/0.42  fof(c_0_24, plain, ![X16, X17, X18]:(~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))|m1_subset_1(k1_relset_1(X16,X17,X18),k1_zfmisc_1(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).
% 0.17/0.42  cnf(c_0_25, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.17/0.42  cnf(c_0_26, negated_conjecture, (m1_subset_1(k8_relat_1(X1,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0)))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.17/0.42  fof(c_0_27, plain, ![X22, X23, X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|k6_relset_1(X22,X23,X24,X25)=k8_relat_1(X24,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_relset_1])])).
% 0.17/0.42  fof(c_0_28, plain, ![X26, X27, X28]:(~v1_relat_1(X28)|(~r1_tarski(k1_relat_1(X28),X26)|~r1_tarski(k2_relat_1(X28),X27)|m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.17/0.42  cnf(c_0_29, plain, (r1_tarski(k2_relat_1(k8_relat_1(X2,X1)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.17/0.42  fof(c_0_30, plain, ![X7, X8]:((~m1_subset_1(X7,k1_zfmisc_1(X8))|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|m1_subset_1(X7,k1_zfmisc_1(X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.17/0.42  cnf(c_0_31, plain, (m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.17/0.42  cnf(c_0_32, negated_conjecture, (k1_relset_1(esk3_0,esk1_0,k8_relat_1(X1,esk4_0))=k1_relat_1(k8_relat_1(X1,esk4_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.17/0.42  cnf(c_0_33, plain, (k6_relset_1(X2,X3,X4,X1)=k8_relat_1(X4,X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.17/0.42  cnf(c_0_34, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.17/0.42  cnf(c_0_35, negated_conjecture, (r1_tarski(k2_relat_1(k8_relat_1(X1,esk4_0)),X1)), inference(spm,[status(thm)],[c_0_29, c_0_19])).
% 0.17/0.42  cnf(c_0_36, negated_conjecture, (v1_relat_1(k8_relat_1(X1,esk4_0))), inference(spm,[status(thm)],[c_0_15, c_0_26])).
% 0.17/0.42  cnf(c_0_37, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.17/0.42  cnf(c_0_38, negated_conjecture, (m1_subset_1(k1_relat_1(k8_relat_1(X1,esk4_0)),k1_zfmisc_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_26])])).
% 0.17/0.42  cnf(c_0_39, negated_conjecture, (~m1_subset_1(k6_relset_1(esk3_0,esk1_0,esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.17/0.42  cnf(c_0_40, negated_conjecture, (k6_relset_1(esk3_0,esk1_0,X1,esk4_0)=k8_relat_1(X1,esk4_0)), inference(spm,[status(thm)],[c_0_33, c_0_16])).
% 0.17/0.42  cnf(c_0_41, negated_conjecture, (m1_subset_1(k8_relat_1(X1,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~r1_tarski(k1_relat_1(k8_relat_1(X1,esk4_0)),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 0.17/0.42  cnf(c_0_42, negated_conjecture, (r1_tarski(k1_relat_1(k8_relat_1(X1,esk4_0)),esk3_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.17/0.42  cnf(c_0_43, negated_conjecture, (~m1_subset_1(k8_relat_1(esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 0.17/0.42  cnf(c_0_44, negated_conjecture, (m1_subset_1(k8_relat_1(X1,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.17/0.42  cnf(c_0_45, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44])]), ['proof']).
% 0.17/0.42  # SZS output end CNFRefutation
% 0.17/0.42  # Proof object total steps             : 46
% 0.17/0.42  # Proof object clause steps            : 25
% 0.17/0.42  # Proof object formula steps           : 21
% 0.17/0.42  # Proof object conjectures             : 19
% 0.17/0.42  # Proof object clause conjectures      : 16
% 0.17/0.42  # Proof object formula conjectures     : 3
% 0.17/0.42  # Proof object initial clauses used    : 11
% 0.17/0.42  # Proof object initial formulas used   : 10
% 0.17/0.42  # Proof object generating inferences   : 12
% 0.17/0.42  # Proof object simplifying inferences  : 7
% 0.17/0.42  # Training examples: 0 positive, 0 negative
% 0.17/0.42  # Parsed axioms                        : 11
% 0.17/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.42  # Initial clauses                      : 15
% 0.17/0.42  # Removed in clause preprocessing      : 0
% 0.17/0.42  # Initial clauses in saturation        : 15
% 0.17/0.42  # Processed clauses                    : 425
% 0.17/0.42  # ...of these trivial                  : 3
% 0.17/0.42  # ...subsumed                          : 160
% 0.17/0.42  # ...remaining for further processing  : 262
% 0.17/0.42  # Other redundant clauses eliminated   : 2
% 0.17/0.42  # Clauses deleted for lack of memory   : 0
% 0.17/0.42  # Backward-subsumed                    : 1
% 0.17/0.42  # Backward-rewritten                   : 19
% 0.17/0.42  # Generated clauses                    : 1048
% 0.17/0.42  # ...of the previous two non-trivial   : 990
% 0.17/0.42  # Contextual simplify-reflections      : 0
% 0.17/0.42  # Paramodulations                      : 1046
% 0.17/0.42  # Factorizations                       : 0
% 0.17/0.42  # Equation resolutions                 : 2
% 0.17/0.42  # Propositional unsat checks           : 0
% 0.17/0.42  #    Propositional check models        : 0
% 0.17/0.42  #    Propositional check unsatisfiable : 0
% 0.17/0.42  #    Propositional clauses             : 0
% 0.17/0.42  #    Propositional clauses after purity: 0
% 0.17/0.42  #    Propositional unsat core size     : 0
% 0.17/0.42  #    Propositional preprocessing time  : 0.000
% 0.17/0.42  #    Propositional encoding time       : 0.000
% 0.17/0.42  #    Propositional solver time         : 0.000
% 0.17/0.42  #    Success case prop preproc time    : 0.000
% 0.17/0.42  #    Success case prop encoding time   : 0.000
% 0.17/0.42  #    Success case prop solver time     : 0.000
% 0.17/0.42  # Current number of processed clauses  : 226
% 0.17/0.42  #    Positive orientable unit clauses  : 57
% 0.17/0.42  #    Positive unorientable unit clauses: 0
% 0.17/0.42  #    Negative unit clauses             : 32
% 0.17/0.42  #    Non-unit-clauses                  : 137
% 0.17/0.42  # Current number of unprocessed clauses: 586
% 0.17/0.42  # ...number of literals in the above   : 1430
% 0.17/0.42  # Current number of archived formulas  : 0
% 0.17/0.42  # Current number of archived clauses   : 34
% 0.17/0.42  # Clause-clause subsumption calls (NU) : 3944
% 0.17/0.42  # Rec. Clause-clause subsumption calls : 2201
% 0.17/0.42  # Non-unit clause-clause subsumptions  : 53
% 0.17/0.42  # Unit Clause-clause subsumption calls : 1002
% 0.17/0.42  # Rewrite failures with RHS unbound    : 0
% 0.17/0.42  # BW rewrite match attempts            : 53
% 0.17/0.42  # BW rewrite match successes           : 3
% 0.17/0.42  # Condensation attempts                : 0
% 0.17/0.42  # Condensation successes               : 0
% 0.17/0.42  # Termbank termtop insertions          : 19091
% 0.17/0.42  
% 0.17/0.42  # -------------------------------------------------
% 0.17/0.42  # User time                : 0.088 s
% 0.17/0.42  # System time              : 0.007 s
% 0.17/0.42  # Total time               : 0.095 s
% 0.17/0.42  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
